import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.General.LinearAlgebra.TensorChains
import New.Spanning.Frames.FiniteShells
import New.Spanning.MainTerm.FillingLevel
import New.Spanning.Unfolding.Climbing

/-!
# Groups that fix given vectors at chosen places have a small mass integral

Let `S` be an admissible filling with base `b = S.b`, and `T` a finite set of finite places of `E`
stable under conjugation. The product `LocProd T` of the completions at `T` is read as one ring,
with integers `R` (`New.Floors.IntegralPlace`), and `F` is a filling datum on it, of modulus
`g = F.levelUnit`. An `F.IntermediateGroup` is a group `Z` with `K(g) ≤ Z ≤ K`, for the integral
unitary group `K` and its congruence subgroup `K(g)` (both `New.unitaryLevel`). `F.groupMeasure` is
a Haar measure on the unitary group, and `F.massIntegral Z` is the mass integral, the number ∫ |∫_Z
χ_g(y x y⁻¹) dy|² dx, where χ_g is `New.Floors.IntegralPlace.extendedBesselChar g`.

* `New.Filling.volume_integers_diff_intUnits_le`: at the chosen places and their conjugates
  (`New.Filling.chosenPlacesAndConj`), few integers are not units.
* `New.Filling.IsFillingData.exists_intermediateGroup_one_place`: for one place `w`, some group `Z`
  contains the elements that fix the given vectors, and `F.massIntegral Z / F.groupMeasure Z` is
  smaller than `F.massIntegral K / F.groupMeasure K` by at least the factor `b ^ (6 * 𝔰.k)` (for no
  place, the factor is `1`). Here `𝔰.k` is the rank of the block `X₀` of the shape `𝔰`. The proof
  takes the stabiliser of the vector at `w`, which has large index in `K`.
* `New.Filling.IsFillingData.exists_intermediateGroup_places`: for several places, take the product;
  the factors multiply. The places of `T` are cut into the fibres `New.Filling.placeFiber` of a map
  `blk`; `New.Filling.evalFiber` and `New.Filling.toFibers` restrict elements of `LocProd T` and
  unitary matrices to the fibres.

Notions from other files:
* `New.Filling`: `S.levelPrime 0` and `S.levelPrime 1` are the level primes `p₀` and `p₁`,
  `S.chosenPlaces i` is the finite set of chosen places of norm `pᵢ`, and `S.ideleM` is the level
  `M = p₀ p₁` as a finite idele.
* `New.Filling.IsFillingData`: `F` is a large lattice datum on `LocProd T` whose modulus is the
  component of `M` at `T` and whose character is `S.charOnPlaces T`.
* `New.Filling.latticeStabilizer`: the integral elements of the finite adelic unitary group;
  `S.reduction` reduces them modulo the chosen places, `S.toPlaces T` takes components at `T`.
* `New.Filling.vectorFixer`: for a chosen place `w` and `d = (ε, v)`, the elements of `S.ResidueGL`
  (the product of the general linear groups over the residue fields) that fix the vector of the span
  of the frame with coordinates `v ≠ 0`, modulo `w` if `ε` is false and modulo its conjugate if `ε`
  is true; `S.fixer Sg d` is the intersection of these groups over `w ∈ Sg`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Filling

open NumberField Matrix Finset Fintype MeasureTheory Valued Floors ENNReal Subgroup Pi
  IntegralPlace

section OnePlace

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-! ### Few integers are not units -/

open scoped Classical in
/-- The chosen places of the filling `S`, above both level primes, and their conjugates. -/
noncomputable def chosenPlacesAndConj (S : Filling E 𝔰) : Finset (FinPlace E) :=
  univ.biUnion fun p : Σ i : Fin 2, S.chosenPlaces i ↦
    {(p.2 : FinPlace E), star (p.2 : FinPlace E)}

theorem mem_chosenPlacesAndConj {S : Filling E 𝔰} {w : FinPlace E} :
    w ∈ S.chosenPlacesAndConj ↔
      ∃ (i : Fin 2) (s : FinPlace E), s ∈ S.chosenPlaces i ∧ (w = s ∨ w = star s) := by
  simp [chosenPlacesAndConj]

/-- Let `S` be a filling over `E` (the data of the filling theorem), whose chosen places
`S.chosenPlaces` lie above its two level primes. Suppose every place of `T` is a chosen place of `S`
or the conjugate of one. Then for each `w ∈ T` the residue field order `w.q` is at least
`S.b ^ 10`. -/
theorem b_pow_ten_le_q {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    (hT : T ⊆ S.chosenPlacesAndConj) {w : FinPlace E} (hw : w ∈ T) :
    S.b ^ 10 ≤ w.q := by
  obtain ⟨i, s, hs, hws⟩ : ∃ (i : Fin 2) (s : FinPlace E),
      s ∈ S.chosenPlaces i ∧ (w = s ∨ w = star s) :=
    mem_chosenPlacesAndConj.1 (hT hw)
  have h_conj : w.q = s.q := by
    obtain rfl | rfl := hws
    · rfl
    · exact q_star s
  rw [h_conj, S.chosenPlaces_q i s hs]
  exact S.le_levelPrime i

/-- If every place of `T` is a chosen place of the filling `S` or the conjugate of one, then `T` has
at most `S.b` elements. -/
theorem card_le_b_of_subset_chosenPlacesAndConj {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    (hT : T ⊆ S.chosenPlacesAndConj) :
    (#T : ℝ) ≤ S.b := by
  classical
  have h_chosen : card (Σ i : Fin 2, S.chosenPlaces i) = 2 * numInfPlaces E := by
    simp [S.card_chosenPlaces]
  have h_pairs : #T ≤ 2 * numInfPlaces E * 2 := by
    grw [hT, chosenPlacesAndConj, card_biUnion_le_card_mul _ _ 2 fun _ _ ↦ card_le_two, card_univ,
      h_chosen]
  have h_real : (#T : ℝ) ≤ 2 * numInfPlaces E * 2 := mod_cast h_pairs
  linarith [S.numInfPlaces_le_div, S.one_le_b]

/-- Let `S` be an admissible filling with base `b = S.b`, let every place of `T` be a chosen place
of `S` or the conjugate of one, and let `P.integers` be the ring of integers of the product
`LocProd T` of the completions at `T`, with units `P.intUnits`. Then (a) `2 ≤ b ^ 9`, and (b) the
integers that are not units have volume at most `(b ^ 9)⁻¹`. -/
theorem volume_integers_diff_intUnits_le [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible]
    {T : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
    (hT : T ⊆ S.chosenPlacesAndConj) :
    2 ≤ ENNReal.ofReal (S.b ^ 9) ∧
    volume (P.integers \ P.intUnits : Set (LocProd T)) ≤ (ENNReal.ofReal (S.b ^ 9))⁻¹ := by
  -- Almost every element of `LocProd T` is a unit (`P.ae_isUnit`), and an integer that is a unit of
  -- `LocProd T` but not of `P.integers` is divisible by the uniformiser `c w` at some `w`. Each
  -- such set of multiples has volume `1 / q ≤ b⁻¹⁰`, and `T` has at most `4 * numInfPlaces E ≤ b`
  -- places.
  classical
  let c (w : T) : (LocProd T)ˣ :=
    MulEquiv.piUnits.symm (mulSingle w (uniformizer (w : FinPlace E)))
  have hb : 1000 ≤ S.b := S.thousand_le_b
  constructor
  · grw [← hb]
    bound
  have h_sub : (P.integers \ P.intUnits : Set (LocProd T)) ≤ᵐ[volume]
      ⋃ w : T, {x : LocProd T | (c w)⁻¹.val * x ∈ integers} := by
    filter_upwards [P.ae_isUnit]
    rintro _ ⟨y, rfl⟩ ⟨hy_int, hy_nonunit⟩
    -- Some component of `y` lies in the maximal ideal, or `y⁻¹` would be integral.
    obtain ⟨j, hj⟩ : ∃ j : T, v (y.val j) < 1 := by
      by_contra! h_one_le
      refine hy_nonunit ⟨hy_int, y, mem_O_locProd.2 fun j ↦ ?_, rfl⟩
      have h_inv : y⁻¹.val j = (y.val j)⁻¹ := by simp
      rw [h_inv, map_inv₀]
      exact inv_le_one_of_one_le₀ (h_one_le j)
    refine Set.mem_iUnion.2 ⟨j, mem_O_locProd.2 fun i ↦ ?_⟩
    obtain rfl | hij : i = j ∨ i ≠ j := eq_or_ne i j
    · have h_comp : ((c i)⁻¹.val * y.val) i = (uniformizer (i : FinPlace E)).val⁻¹ * y.val i := by
        simp [c]
      rw [h_comp]
      exact v_uniformizer_inv_mul_le_one_iff.2 hj
    · have h_comp : ((c j)⁻¹.val * y.val) i = y.val i := by simp [c, hij]
      rw [h_comp]
      exact mem_O_locProd.1 hy_int i
  have h_vol (w : T) :
      volume {x : LocProd T | (c w)⁻¹.val * x ∈ integers} ≤ ENNReal.ofReal (S.b ^ 10)⁻¹ := by
    have h_q : S.b ^ 10 ≤ (w : FinPlace E).q := b_pow_ten_le_q hT w.prop
    have h_eq : volume {x : LocProd T | (c w)⁻¹.val * x ∈ integers} =
        ENNReal.ofReal ((w : FinPlace E).q : ℝ)⁻¹ := by
      rw [volume_setOf_mul_mem, modulus_eq_inv_genIndex, genIndex_eq_inv_prod_norm,
        Fintype.prod_eq_single w]
      · simp [c, norm_locField_eq_q_zpow]
      · intro i hi
        simp [c, hi]
    rw [h_eq]
    gcongr
  have h_card : (#T : ℝ) ≤ S.b := card_le_b_of_subset_chosenPlacesAndConj hT
  calc volume (P.integers \ P.intUnits : Set (LocProd T))
    _ ≤ ∑ w : T, volume {x : LocProd T | (c w)⁻¹.val * x ∈ integers} :=
      (measure_mono_ae h_sub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _ : T, ENNReal.ofReal (S.b ^ 10)⁻¹ := sum_le_sum fun w _ ↦ h_vol w
    _ = ENNReal.ofReal (#T * (S.b ^ 10)⁻¹) := by
      rw [sum_const, card_univ, card_coe, ← ofReal_nsmul, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (S.b * (S.b ^ 10)⁻¹) := by gcongr
    _ = (ENNReal.ofReal (S.b ^ 9))⁻¹ := by
      rw [← ofReal_inv_of_pos (by positivity)]
      congr 1
      field_simp

/-! ### One place -/

/-- If `2 ≤ B` and `B ^ (t + 1) * z ≤ k` in `ℝ≥0∞`, then `(z + B⁻¹ ^ (t + 1) * k) * B ^ t ≤ k`. -/
theorem add_inv_pow_mul_mul_pow_le {B z k : ℝ≥0∞} {t : ℕ} (hB : 2 ≤ B) (hz : B ^ (t + 1) * z ≤ k) :
    (z + B⁻¹ ^ (t + 1) * k) * B ^ t ≤ k := by
  -- Both terms times `B ^ (t + 1)` are at most `k`; the spare factor `B ≥ 2` pays for the sum.
  rw [← ENNReal.mul_le_mul_iff_left two_ne_zero ofNat_ne_top]
  calc (z + B⁻¹ ^ (t + 1) * k) * B ^ t * 2
    _ ≤ (z + B⁻¹ ^ (t + 1) * k) * B ^ t * B := by gcongr
    _ = B ^ (t + 1) * z + (B⁻¹ * B) ^ (t + 1) * k := by ring
    _ ≤ k * 2 := by grw [hz, ENNReal.inv_mul_le_one, one_pow, one_mul, mul_two]

/-- Let `S` be a filling of shape `𝔰` over `E` (the data of the filling theorem, with `𝔰.ϱ`
hyperbolic planes, a definite space X₀ and a vector z). Let `T` be a finite set of places stable
under conjugation, and `P.integers` the ring of integers of the product `LocProd T` of the
completions at `T`. The form `(S.latticeMiddle A).splitGram` over a ring `A` consists of `𝔰.ϱ`
hyperbolic planes and the Gram matrix `S.latticeMiddle A` of X₀ ⊕ Ez in the lattice basis. Taking
components at `T` (`S.toPlaces T`) maps the integral elements `S.latticeStabilizer` of the finite
adelic unitary group of `S` onto `unitaryLevel P.integers 1`. -/
theorem range_toPlaces_latticeStabilizer [WeilData E] {S : Filling E 𝔰} {T : Finset (FinPlace E)}
    [fT : T.StarStable] [P : IntegralPlace (LocProd T)] :
    ((S.toPlaces T).comp S.latticeStabilizer.subtype).range =
      unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨-, hk_int⟩ : S.IsIntegralOff T k ∧
        S.toPlaces T k ∈ unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram :=
      S.mem_latticeStabilizer_iff.1 k.prop
    exact hk_int
  · intro hy
    obtain ⟨x, rfl, hx_off, -⟩ := exists_isIntegralOff_toPlaces_eq y
    have hx_int : x ∈ S.latticeStabilizer := S.mem_latticeStabilizer_iff.2 ⟨hx_off, hy⟩
    exact ⟨⟨x, hx_int⟩, rfl⟩

section Reduction

variable {S : Filling E 𝔰}

/-- The level `M = S.ideleM`, the product of the two level primes as a finite idele, lies in the
maximal ideal at every chosen place `w`. -/
theorem v_ideleM_lt_one {i : Fin 2} (w : S.chosenPlaces i) : v (S.ideleM.val w) < 1 := by
  obtain ⟨h_zero, -⟩ : New.reduceAt w (S.M : Ô E) = 0 ∧ New.reduceAt w (star (S.M : Ô E)) = 0 :=
    (S.M_dvd_iff S.M).1 dvd_rfl ⟨i, w⟩
  rw [reduceAt_eq_zero, SubringClass.coe_natCast] at h_zero
  rwa [ideleM_val]

/-- Let `w` be a chosen place and `r` an integral finite adele. If `M⁻¹ r` is integral at `w`, for
the level `M = S.ideleM`, then `r` vanishes modulo `w`. -/
theorem reduceAt_eq_zero_of_inv_ideleM_smul {i : Fin 2} (w : S.chosenPlaces i) {r : Ô E}
    (hr : v ((S.ideleM⁻¹ • (r : 𝔸f E)) w) ≤ 1) :
    New.reduceAt w r = 0 := by
  have h_adele : (r : 𝔸f E) = S.ideleM.val * S.ideleM⁻¹ • (r : 𝔸f E) := by simp [Units.smul_def]
  have h_factor : (r : 𝔸f E) w = S.ideleM.val w * (S.ideleM⁻¹ • (r : 𝔸f E)) w := by
    simpa only [map_mul, evalAt_apply] using congrArg (evalAt (w : FinPlace E)) h_adele
  rw [reduceAt_eq_zero, h_factor, map_mul]
  exact (mul_le_of_le_one_right' hr).trans_lt (v_ideleM_lt_one w)

/-- If the inverse of the level `M = S.ideleM` is integral at all places outside `T₀`, then `T₀`
contains every chosen place. -/
theorem mem_of_inv_ideleM_mem_integralOff {T₀ : Finset (FinPlace E)}
    (hT : (↑S.ideleM⁻¹ : 𝔸f E) ∈ integralOff T₀) {i : Fin 2} (w : S.chosenPlaces i) :
    (w : FinPlace E) ∈ T₀ := by
  -- Otherwise `M⁻¹` is integral at `w`, and `1` vanishes modulo `w`.
  by_contra hw
  have h_int : v ((S.ideleM⁻¹ • ((1 : Ô E) : 𝔸f E)) w) ≤ 1 := by
    simpa [Units.smul_def] using (mem_integralOff T₀).1 hT w hw
  have h_zero : New.reduceAt w (1 : Ô E) = 0 := reduceAt_eq_zero_of_inv_ideleM_smul w h_int
  simp at h_zero

/-- Let `F` be a filling datum at `T`: a large lattice datum on the product of the completions at
`T` whose modulus `g` is the component of the level `S.ideleM = p₀ p₁`. Let `w ∈ T` be a chosen
place. An integral element `k` of the adelic unitary group whose component at `T` lies in the
congruence subgroup `K(g) = F.congruenceSubgroup` has reduction `S.reduction k i w = 1` modulo
`w`. -/
theorem IsFillingData.reduction_eq_one {T : Finset (FinPlace E)} [fT : T.StarStable]
    [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (h : S.IsFillingData T F) {i : Fin 2}
    {w : S.chosenPlaces i} (hw : (w : FinPlace E) ∈ T) {k : S.latticeStabilizer}
    (hk : S.toPlaces T k ∈ F.congruenceSubgroup) :
    S.reduction k i w = 1 := by
  -- Each entry of `M⁻¹ (k - 1)` is integral at `w`, so each entry of `k - 1` vanishes modulo `w`.
  let x : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (k : S.GFin).val
  let y : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T) := (S.toPlaces T k).val
  have hy : y = x.map (evalPlaces T) := rfl
  have h_map : F.levelUnit⁻¹ • (y - 1) = (S.ideleM⁻¹ • (x - 1)).map (evalPlaces T) := by
    ext1 a b
    simp [h.levelUnit_eq, hy, Units.smul_def, Matrix.one_apply, apply_ite (evalPlaces T)]
  have h_cong : IsIntMatrix integers (F.levelUnit⁻¹ • (y - 1)) := (mem_unitaryLevel_def.1 hk).right
  rw [h_map] at h_cong
  refine intGL.map_eq_one.2 fun a b ↦ reduceAt_eq_zero_of_inv_ideleM_smul w ?_
  change v (evalPlaces T ((S.ideleM⁻¹ • (x - 1)) a b) ⟨w, hw⟩) ≤ 1
  exact mem_O_locProd.1 (h_cong a b) ⟨w, hw⟩

/-- Let `S` be an admissible filling, `w` a chosen place above the level prime
`p = S.levelPrime i`, and `d` a nonzero vector modulo `w` or its conjugate. The integral elements
whose reduction fixes `d` (lies in `S.vectorFixer w d`) have index `p ^ r - 1` in the integral group
`S.latticeStabilizer`, where `r = 𝔰.r` is the size of the matrices. -/
theorem index_comap_vectorFixer [S.IsAdmissible] {i : Fin 2} (w : S.chosenPlaces i)
    (d : S.FrameVector w) :
    ((S.vectorFixer w d).comap S.reduction).index = S.levelPrime i ^ 𝔰.r - 1 := by
  classical
  -- `S.reduction` and the component at `w` are onto, and the stabiliser of a nonzero vector has as
  -- index the number of nonzero vectors.
  obtain ⟨ε, u, hu⟩ := d
  have h_inj :
      Function.Injective (inclMatrix (ResField (w : FinPlace E)) 𝔰.besselFrame).mulVecLin :=
    inclMatrix_mulVecLin_injective ⟨𝔰.besselFrame, besselFrame_injective⟩ _
  have h_ne : inclMatrix (ResField (w : FinPlace E)) 𝔰.besselFrame *ᵥ u ≠ 0 := by
    simpa using h_inj.ne hu
  have h_surj : Function.Surjective fun s : S.ResidueGL ↦ S.idOrInvAdjoint ε (s i w) :=
    fun g ↦ ⟨mulSingle i (mulSingle w ((S.idOrInvAdjoint ε).symm g)), by simp⟩
  rw [index_comap_of_surjective _ IsAdmissible.reduction_surjective, vectorFixer,
    index_comap_of_surjective _ h_surj, index_stabilizer_GL_vector h_ne,
    card_resField_eq_levelPrime]

/-- Let `𝔰` be the shape of a filling, with the numbers `k = 𝔰.k`, `n = 𝔰.n` and the matrix size
`r = 𝔰.r`. Some `t` has `t + 1 + n + 2 · 10⁹ n⁴ ≤ k`, `6 k ≤ 9 t` and `t + 1 < r`. -/
theorem exists_exponent_le_k (S : Filling E 𝔰) :
    ∃ t : ℕ, t + 1 + 𝔰.n + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k ∧ 6 * 𝔰.k ≤ 9 * t ∧ t + 1 < 𝔰.r := by
  have h_pow : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧ 3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k :=
    S.pow_chain
  have h_size : 𝔰.r = 𝔰.ϱ + (𝔰.k + 1 + 𝔰.ϱ) := by simp
  have h_pos : 0 < 𝔰.n ^ 4 := by positivity
  have h_le : 𝔰.n ≤ 𝔰.n ^ 4 := Nat.le_self_pow (by norm_num) _
  exact ⟨𝔰.k - 10 ^ 10 * 𝔰.n ^ 4, by omega⟩

end Reduction

variable [WeilData E] {S : Filling E 𝔰} [S.IsAdmissible]
  {T T₀ : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

/-- Let `S` be an admissible filling with base `b = S.b`, and `F` a filling datum at `T`, where
every place of `T` is a chosen place or the conjugate of one. Let `K = unitaryLevel P.integers 1 _`
be the integral unitary group over the completions at `T` and `K(g) = F.congruenceSubgroup` its
subgroup of elements congruent to `1` modulo `g`. Let `Z` with `K(g) ≤ Z ≤ K` have index
`p₀ ^ r - 1` in `K`, for the first level prime `p₀` and the size `r = 𝔰.r` of the matrices. Then
`ϰ(Z) vol(K) b ^ (6 k) ≤ ϰ(K) vol(Z)`. Here `vol = F.groupMeasure` is a Haar measure,
`ϰ(Z) = F.massIntegral Z` is ∫ |∫_Z χ_g(y x y⁻¹) dy|² dx for the function
χ_g = `extendedBesselChar g`, and `k = 𝔰.k` is the rank of the block `X₀` of the shape `𝔰`. -/
theorem IsFillingData.massIntegral_mul_le_of_relIndex_eq (h : S.IsFillingData T F)
    (hT : T ⊆ S.chosenPlacesAndConj) (Z : F.IntermediateGroup)
    (h_index : Z.val.relIndex (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) =
      S.levelPrime 0 ^ 𝔰.r - 1) :
    F.massIntegral Z *
          F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
        ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ≤
      F.massIntegral (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
        F.groupMeasure Z := by
  -- The large index makes the volume of `Z` small; then
  -- `IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error` bounds the mass integral of
  -- `Z` from above, `IntegralPlace.IsLargeLatticeData.setLIntegral_congruenceSubgroup_integral_sq`
  -- that of `K` from below.
  set μ : Measure (U (S.latticeMiddle (LocProd T)).splitGram) := F.groupMeasure
  set K : Subgroup (U (S.latticeMiddle (LocProd T)).splitGram) :=
    unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram with hK
  -- With `B = b ^ 9` the non-units have volume at most `B⁻¹`; the gain is `B ^ t`, `6 k ≤ 9 t`.
  set B : ℝ≥0∞ := ENNReal.ofReal (S.b ^ 9) with hB
  obtain ⟨hB_two, h_vol⟩ : 2 ≤ B ∧ volume (P.integers \ P.intUnits : Set (LocProd T)) ≤ B⁻¹ :=
    S.volume_integers_diff_intUnits_le hT
  have hb : 1 ≤ S.b := S.one_le_b
  obtain ⟨t, ht_le, ht_gain, ht_lt⟩ :
      ∃ t : ℕ, t + 1 + 𝔰.n + 2 * 10 ^ 9 * 𝔰.n ^ 4 ≤ 𝔰.k ∧ 6 * 𝔰.k ≤ 9 * t ∧ t + 1 < 𝔰.r :=
    S.exists_exponent_le_k
  have h_rare : B ^ (t + 1) * μ Z ≤ μ K := by
    have hB_le : B ≤ S.levelPrime 0 := by
      grw [hB, pow_le_pow_right₀ hb (Nat.le_succ 9), S.le_levelPrime 0, ofReal_natCast]
    have h_prime : (S.levelPrime 0).Prime := (S.levelPrime_prime_and_ne 0).left
    have h_pow_le : S.levelPrime 0 ^ (t + 1) ≤ Z.val.relIndex K := by
      rw [h_index]
      exact Nat.le_sub_one_of_lt (pow_lt_pow_right₀ h_prime.one_lt ht_lt)
    calc B ^ (t + 1) * μ Z
      _ ≤ (S.levelPrime 0 ^ (t + 1) : ℕ) * μ Z := by grw [hB_le, Nat.cast_pow]
      _ ≤ Z.val.relIndex K * μ Z := by gcongr
      _ = μ K := by
        rw [hK, ← relIndex_mul_measure_inf unitaryLevel_open_compact.right Z.isOpen,
          inf_of_le_left Z.prop.right]
  have h_K : 2⁻¹ ^ 𝔰.n ≤ μ K := by
    rw [hK]
    exact h.inv_two_pow_le_groupMeasure ⟨hB_two, h_vol⟩
  have h_upper : F.massIntegral Z ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1) * μ K) := by
    have h_modulus (c : (LocProd T)ˣ) (hc : c.val ∈ integers) (hc_inv : c⁻¹.val ∉ integers) :
        P.modulus c ≤ B⁻¹ := (IsLargeLatticeData.modulus_le_volume_nonunits c hc hc_inv).trans h_vol
    have h_half : B⁻¹ ^ 𝔰.n ≤ 2⁻¹ ^ 𝔰.n := by gcongr
    calc F.massIntegral Z
      _ ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1 + 𝔰.n)) :=
        h.massIntegral_le_main_add_error Z hB_two h_modulus ht_le
      _ ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1) * μ K) := by
        grw [pow_add B⁻¹ (t + 1), h_half, h_K]
  have h_lower : μ K ^ 2 * μ F.congruenceSubgroup ≤ F.massIntegral K := by
    have hK_mem : K ∈ Set.Icc F.congruenceSubgroup K := ⟨unitaryLevel_le_unitaryLevel_one, le_rfl⟩
    -- The left side is the part of the outer integral over `K(g)`.
    rw [← h.setLIntegral_congruenceSubgroup_integral_sq ⟨K, hK_mem⟩]
    exact setLIntegral_le_lintegral _ _
  have h_gain : ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ≤ B ^ t := by
    grw [pow_le_pow_right₀ hb ht_gain, pow_mul, ofReal_pow (by positivity)]
  calc F.massIntegral Z * μ K * ENNReal.ofReal (S.b ^ (6 * 𝔰.k))
    _ ≤ μ Z * μ F.congruenceSubgroup * (μ Z + B⁻¹ ^ (t + 1) * μ K) * μ K * B ^ t := by
      grw [h_upper, h_gain]
    _ = μ Z * μ F.congruenceSubgroup * μ K * ((μ Z + B⁻¹ ^ (t + 1) * μ K) * B ^ t) := by ring
    _ ≤ μ Z * μ F.congruenceSubgroup * μ K * μ K := by
      grw [add_inv_pow_mul_mul_pow_le hB_two h_rare]
    _ = μ K ^ 2 * μ F.congruenceSubgroup * μ Z := by ring
    _ ≤ F.massIntegral K * μ Z := by grw [h_lower]

/-- Let `S` be an admissible filling and `F` a filling datum at `T`, of modulus `g`. Let `Sg` be a
set of chosen places above the first level prime, `d w` a nonzero vector modulo `w` or its
conjugate, and let the inverse of the level `S.ideleM` be integral off `T₀`. Let `o` be `none`, or a
place `w` of `Sg` such that `T` consists of the places of `T₀` equal to `w` or `w̄`. Then some group
`Z` with `K(g) ≤ Z ≤ K`, for the integral unitary group `K = unitaryLevel P.integers 1 _` and its
congruence subgroup `K(g) = F.congruenceSubgroup`, has two properties. (a) `Z` contains the
`T`-component of every integral element whose reduction fixes `d w` for all `w ∈ Sg`. (b) With the
mass integral `ϰ = F.massIntegral` and `vol = F.groupMeasure`, `ϰ(Z) vol(K) B ≤ ϰ(K) vol(Z)`, where
`B` is `S.b ^ (6 * 𝔰.k)` if `o` is a place, and `1` otherwise. -/
theorem IsFillingData.exists_intermediateGroup_one_place (h : S.IsFillingData T F)
    (Sg : Finset (S.chosenPlaces 0)) (o : Option Sg)
    (d : ∀ w : S.chosenPlaces 0, S.FrameVector w)
    (hT : (↑S.ideleM⁻¹ : 𝔸f E) ∈ integralOff T₀)
    (h_places : ∀ w ∈ o, ∀ j : FinPlace E, j ∈ T ↔ j ∈ T₀ ∧ (j = w ∨ star j = w)) :
    ∃ Z : F.IntermediateGroup,
      -- (a)
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      -- (b)
      F.massIntegral Z *
            F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          o.elim 1 (fun _ : Sg ↦ ENNReal.ofReal (S.b ^ (6 * 𝔰.k))) ≤
        F.massIntegral (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          F.groupMeasure Z := by
  classical
  -- Without a place take `Z = K`. At a place `w` take for `Z` the image of the group `H` of those
  -- `k` whose reduction at `w` fixes the vector; its index in `K` is that of `H`.
  let p : S.latticeStabilizer →* U (S.latticeMiddle (LocProd T)).splitGram :=
    (S.toPlaces T).comp S.latticeStabilizer.subtype
  have h_range : p.range = unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram :=
    range_toPlaces_latticeStabilizer
  obtain _ | ⟨w, hw⟩ := o
  · let K : F.IntermediateGroup := ⟨unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram,
      unitaryLevel_le_unitaryLevel_one, le_rfl⟩
    exact ⟨K, fun k _ ↦ h_range.le ⟨k, rfl⟩, by simp [K]⟩
  replace h_places (j : FinPlace E) : j ∈ T ↔ j ∈ T₀ ∧ (j = w ∨ star j = w) :=
    h_places ⟨w, hw⟩ rfl j
  have hwT : (w : FinPlace E) ∈ T :=
    (h_places w).2 ⟨mem_of_inv_ideleM_mem_integralOff hT w, .inl rfl⟩
  have hT_sub : T ⊆ S.chosenPlacesAndConj := by
    intro j hj
    have hjw : j = w ∨ star j = w := ((h_places j).1 hj).right
    exact mem_chosenPlacesAndConj.2 ⟨0, w, w.prop, hjw.imp_right fun h_star ↦ by simp [← h_star]⟩
  let H : Subgroup S.latticeStabilizer := (S.vectorFixer w (d w)).comap S.reduction
  have h_cong : F.congruenceSubgroup.comap p ≤ H := by
    intro k hk
    have h_one : S.reduction k 0 w = 1 := h.reduction_eq_one hwT hk
    simp [H, vectorFixer, h_one]
  have h_lower : F.congruenceSubgroup ≤ H.map p := by
    have h_le_range : F.congruenceSubgroup ≤ p.range :=
      unitaryLevel_le_unitaryLevel_one.trans h_range.ge
    rw [← map_comap_eq_self h_le_range]
    exact map_mono h_cong
  have h_upper : H.map p ≤ unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram :=
    (H.map_le_range p).trans h_range.le
  have h_index :
      (H.map p).relIndex (unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram) =
        S.levelPrime 0 ^ 𝔰.r - 1 := by
    have h_ker : p.ker ≤ H := (p.ker_le_comap F.congruenceSubgroup).trans h_cong
    rw [← h_range, ← index_comap, comap_map_eq_self h_ker]
    exact index_comap_vectorFixer w (d w)
  let Z : F.IntermediateGroup := ⟨H.map p, h_lower, h_upper⟩
  refine ⟨Z, fun k hk ↦ ⟨k, mem_fixer.1 hk w hw, rfl⟩, ?_⟩
  simpa only [Option.elim_some] using h.massIntegral_mul_le_of_relIndex_eq hT_sub Z h_index

end OnePlace

/-! ### Restriction to the fibres of a map on places -/

section Rings

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-- The places of `T` that the map `blk` sends to `i`. -/
abbrev placeFiber (T : Finset (FinPlace E)) {ι : Type} [DecidableEq ι] (blk : FinPlace E → ι)
    (i : ι) : Finset (FinPlace E) :=
  {w ∈ T | blk w = i}

/-- The projection from the product of the completions at `T` to the product of the completions at
the places of `T` that `blk` sends to `i`. -/
noncomputable def evalFiber (T : Finset (FinPlace E)) {ι : Type} [DecidableEq ι]
    (blk : FinPlace E → ι) (i : ι) : LocProd T →+* LocProd (placeFiber T blk i) :=
  RingHom.pi fun w : placeFiber T blk i ↦
    evalRingHom _ (⟨w, mem_of_mem_filter (w : FinPlace E) w.prop⟩ : T)

variable {S : Filling E 𝔰} {T : Finset (FinPlace E)} {ι : Type} [DecidableEq ι]
  (blk : FinPlace E → ι)

/-- The projection to a fibre of `blk` keeps the component at each place `w` of the fibre. -/
lemma evalFiber_apply (i : ι) (x : LocProd T) (w : placeFiber T blk i) :
    evalFiber T blk i x w = x ⟨w, mem_of_mem_filter (w : FinPlace E) w.prop⟩ :=
  rfl

/-- A property holds at all places of `T` if and only if it holds on each fibre
`placeFiber T blk i` of the map `blk`. -/
lemma forall_placeFiber {E : Type} [Field E] {T : Finset (FinPlace E)} {ι : Type} [DecidableEq ι]
    (blk : FinPlace E → ι) {p : T → Prop} :
    (∀ w : T, p w) ↔
      ∀ (i : ι) (w : placeFiber T blk i), p ⟨w, mem_of_mem_filter (w : FinPlace E) w.prop⟩ :=
  ⟨fun hp _ _ ↦ hp _, fun hp w ↦ hp (blk w) ⟨w, mem_filter.2 ⟨w.prop, rfl⟩⟩⟩

/-- Two elements of the product of the completions at `T` are equal if and only if their
projections to each fibre of `blk` are equal. -/
lemma eq_iff_evalFiber_eq {x y : LocProd T} :
    x = y ↔ ∀ i : ι, evalFiber T blk i x = evalFiber T blk i y := by
  simp only [funext_iff, evalFiber_apply]
  exact forall_placeFiber blk

/-- An element of the product of the completions at `T` is integral if and only if its projection
to each fibre of `blk` is integral. -/
lemma mem_O_iff_evalFiber_mem {x : LocProd T} :
    x ∈ SemilocalField.O ↔ ∀ i : ι, evalFiber T blk i x ∈ SemilocalField.O := by
  simp only [mem_O_locProd, evalFiber_apply]
  exact forall_placeFiber blk

/-- When `T` is cut into the fibres of a map `blk`, the additive character `S.charOnPlaces T` of the
product of the completions at `T`, which is the character of the finite adeles of `S` after
extension by zero, is the product of the characters of the fibres. -/
theorem charOnPlaces_eq_prod_fibers [Fintype ι] (x : LocProd T) :
    S.charOnPlaces T x = ∏ i : ι, S.charOnPlaces (placeFiber T blk i) (evalFiber T blk i x) := by
  classical
  -- An adele supported on `T` is the sum of its parts on the fibres.
  have h_sum :
      adeleOfLocal T x = ∑ i : ι, adeleOfLocal (placeFiber T blk i) (evalFiber T blk i x) := by
    ext1 w
    rw [← evalAt_apply, ← evalAt_apply, map_sum]
    simp only [evalAt_apply, adeleOfLocal_apply, evalFiber_apply]
    -- A place of `T` lies in exactly one fibre; both sides vanish at the other places.
    by_cases hw : w ∈ T <;> simp [hw]
  simp only [charOnPlaces, AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_ofClass, h_sum,
    AddChar.map_sum_eq_prod]

end Rings

section Groups

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-- The map from the unitary group over the completions at `T` to the product of the unitary groups
over the fibres of `blk`, given by the projections `evalFiber T blk i` on matrix entries. -/
noncomputable def toFibers (S : Filling E 𝔰) (T : Finset (FinPlace E)) [fT : T.StarStable]
    {ι : Type} [DecidableEq ι] (blk : FinPlace E → ι)
    [∀ i : ι, (placeFiber T blk i).StarStable] :
    U (S.latticeMiddle (LocProd T)).splitGram →*
      ∀ i : ι, U (S.latticeMiddle (LocProd (placeFiber T blk i))).splitGram :=
  MonoidHom.pi fun i : ι ↦
    U.map (evalFiber T blk i) (fun _ ↦ rfl) (S.map_splitGram_latticeMiddle (evalFiber T blk i))

variable {S : Filling E 𝔰} {T : Finset (FinPlace E)} [fT : T.StarStable]
  {ι : Type} [DecidableEq ι] (blk : FinPlace E → ι) [∀ i : ι, (placeFiber T blk i).StarStable]

/-- For a unitary matrix `x` over the completions at `T`, the entries of its component
`S.toFibers T blk x i` at the fibre of `blk` over `i` are the projections of the entries of `x`. -/
lemma toFibers_apply (x : U (S.latticeMiddle (LocProd T)).splitGram) (i : ι) (a b : 𝔰.BesselIndex) :
    (S.toFibers T blk x i).val a b = evalFiber T blk i (x.val a b) :=
  rfl

/-- For an adelic unitary matrix `x`, restricting its components at `T` to a fibre of `blk` gives
the components of `x` at that fibre. -/
lemma toFibers_toPlaces (x : U (S.latticeMiddle (𝔸f E)).splitGram) (i : ι) :
    S.toFibers T blk (S.toPlaces T x) i = S.toPlaces (placeFiber T blk i) x :=
  rfl

/-- Unitary matrices over the fibres of `blk` glue to a unitary matrix over `T`, that is, the map
`S.toFibers T blk` to the product of the unitary groups over the fibres is onto. -/
lemma toFibers_surjective : Function.Surjective (S.toFibers T blk) := by
  intro y
  let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T) :=
    of fun (a b : 𝔰.BesselIndex) (w : T) ↦ (y (blk w)).val a b ⟨w, mem_filter.2 ⟨w.prop, rfl⟩⟩
  have hM (i : ι) : M.map (evalFiber T blk i) = (y i).val := by
    ext a b ⟨w, hw⟩
    obtain rfl : blk w = i := (mem_filter.1 hw).2
    rfl
  have h_fiber (i : ι) :
      (Mᴴ * (S.latticeMiddle (LocProd T)).splitGram * M).map (evalFiber T blk i) =
        (S.latticeMiddle (LocProd T)).splitGram.map (evalFiber T blk i) := by
    rw [map_conjTranspose_mul_mul _ fun _ ↦ rfl, hM, S.map_splitGram_latticeMiddle]
    exact mem_U.1 (y i).prop
  have h_unitary : Mᴴ * (S.latticeMiddle (LocProd T)).splitGram * M =
      (S.latticeMiddle (LocProd T)).splitGram := by
    ext a b : 1
    exact (eq_iff_evalFiber_eq blk).2 fun i ↦ congr_fun₂ (h_fiber i) a b
  refine ⟨U.of IsHermitianUnit.isUnit M h_unitary, ?_⟩
  ext i : 3
  exact hM i

/-- A unitary matrix over the completions at `T` is integral with integral inverse and congruent to
`1` modulo `u`, that is, lies in `unitaryLevel SemilocalField.O u`, if and only if its components
at all fibres of `blk` satisfy the same for the projections of `u`. -/
lemma mem_unitaryLevel_iff_toFibers {u : (LocProd T)ˣ}
    {x : U (S.latticeMiddle (LocProd T)).splitGram} :
    x ∈ unitaryLevel SemilocalField.O u (S.latticeMiddle (LocProd T)).splitGram ↔
      ∀ i : ι, S.toFibers T blk x i ∈ unitaryLevel SemilocalField.O (u.map (evalFiber T blk i))
        (S.latticeMiddle (LocProd (placeFiber T blk i))).splitGram := by
  -- Each of the three conditions asks for a matrix to be integral, which is read fibre by fibre.
  have h_int (M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) :
      IsIntMatrix SemilocalField.O M ↔
        ∀ i : ι, IsIntMatrix SemilocalField.O (M.map (evalFiber T blk i)) :=
    ⟨fun hM i a b ↦ (mem_O_iff_evalFiber_mem blk).1 (hM a b) i,
      fun hM a b ↦ (mem_O_iff_evalFiber_mem blk).2 fun i ↦ hM i a b⟩
  have h_cong (i : ι) : (u⁻¹ • (x.val.val - 1)).map (evalFiber T blk i) =
      (u.map (evalFiber T blk i) : (LocProd (placeFiber T blk i))ˣ)⁻¹ •
        ((S.toFibers T blk x i).val.val - 1) := by
    ext a b : 1
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, Units.smul_def, smul_eq_mul,
      map_mul, map_sub, Units.coe_map_inv, MonoidHom.coe_ofClass, toFibers_apply, Matrix.one_apply,
      apply_ite (evalFiber T blk i), map_one, map_zero]
  have h_map (y : U (S.latticeMiddle (LocProd T)).splitGram) (i : ι) :
      (S.toFibers T blk y i).val.val = y.val.val.map (evalFiber T blk i) := rfl
  have h_map_inv (i : ι) :
      (S.toFibers T blk x i).val⁻¹.val = x.val⁻¹.val.map (evalFiber T blk i) := h_map x⁻¹ i
  simp only [mem_unitaryLevel_def, mem_intGL, forall_and, ← h_cong, ← h_int]
  simp only [h_map, h_map_inv]
  -- The congruences agree; `x` and `x⁻¹` are integral when they are so on every fibre.
  exact and_congr_left' (and_congr (h_int x.val.val) (h_int x⁻¹.val.val))

/-- The group `unitaryLevel SemilocalField.O u` for the Gram matrix `splitGram` over the completions
at `T` is the preimage under `S.toFibers T blk` of the product, over all `i`, of the same groups
over the fibres of `blk`. For each `i`, the modulus there is `u` projected by
`evalFiber T blk i`. -/
lemma unitaryLevel_eq_comap_toFibers {u : (LocProd T)ˣ} :
    unitaryLevel SemilocalField.O u (S.latticeMiddle (LocProd T)).splitGram =
      (Subgroup.pi Set.univ fun i : ι ↦ unitaryLevel SemilocalField.O (u.map (evalFiber T blk i))
        (S.latticeMiddle (LocProd (placeFiber T blk i))).splitGram).comap (S.toFibers T blk) := by
  ext x
  simp [Subgroup.mem_pi, mem_unitaryLevel_iff_toFibers blk]

/-- A unitary matrix over the completions at `T` lies in `besselU`, the group of unitary matrices
that are unitriangular for the levels of the indices, if and only if this holds on each fibre of
`blk`. -/
lemma mem_besselU_iff_toFibers {x : U (S.latticeMiddle (LocProd T)).splitGram} :
    x ∈ besselU ↔ ∀ i : ι, S.toFibers T blk x i ∈ besselU := by
  have h_entry (a b : 𝔰.BesselIndex) :
      x.val a b = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd T)) a b ↔
        ∀ i : ι, (S.toFibers T blk x i).val a b =
          (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (LocProd (placeFiber T blk i))) a b := by
    rw [eq_iff_evalFiber_eq blk]
    simp [toFibers_apply, Matrix.one_apply, apply_ite (evalFiber T blk _)]
  simp only [mem_besselU, h_entry]
  exact ⟨fun hx i a b hab ↦ hx a b hab i, fun hx a b hab i ↦ hx i a b hab⟩

end Groups

section Measures

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {T : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
  {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}
  {ι : Type} [DecidableEq ι] (blk : FinPlace E → ι) [∀ i : ι, (placeFiber T blk i).StarStable]
  [Fintype ι] [P' : ∀ i : ι, IntegralPlace (LocProd (placeFiber T blk i))]

/-- The map `S.toFibers T blk` from the unitary group over the completions at `T` to the product of
the unitary groups over the fibres of `blk` is a measurable embedding. -/
lemma measurableEmbedding_toFibers : MeasurableEmbedding (S.toFibers T blk) := by
  -- The projection to each fibre is continuous entry by entry, and the map is injective.
  have h_cont : Continuous (S.toFibers T blk) :=
    continuous_pi fun i : ι ↦ U.continuous_map (continuous_pi fun _ ↦ continuous_apply _)
      (hf_star := fun _ ↦ rfl) (hJ_map := S.map_splitGram_latticeMiddle (evalFiber T blk i))
  refine h_cont.measurableEmbedding fun x y hxy ↦ ?_
  ext a b : 3
  refine (eq_iff_evalFiber_eq blk).2 fun i ↦ ?_
  rw [← toFibers_apply, ← toFibers_apply, hxy]

/-- Let `blk` send the places to indices in a finite type `ι`, and let the additive characters of
the integral places `P` at `T` and `P' i` at the fibres of `blk` be those of `S`. The function
`extendedBesselChar a` is the product of the same functions of the fibres. -/
lemma extendedBesselChar_eq_prod_toFibers (hψ : P.ψ = S.charOnPlaces T)
    (hψ' : ∀ i : ι, (P' i).ψ = S.charOnPlaces (placeFiber T blk i))
    (a : (LocProd T)ˣ) (x : U (S.latticeMiddle (LocProd T)).splitGram) :
    extendedBesselChar a x = ∏ i : ι, extendedBesselChar (a.map (evalFiber T blk i))
      (S.toFibers T blk x i) := by
  -- On `besselU` times the congruence subgroup `extendedBesselChar` is a value of the character,
  -- which is a product.
  by_cases hx : ∃ u ∈ besselU,
      u⁻¹ * x ∈ unitaryLevel integers a (S.latticeMiddle (LocProd T)).splitGram
  · obtain ⟨(u : (S.latticeMiddle (LocProd T)).G), hu, hux⟩ := hx
    have h_fiber (i : ι) : extendedBesselChar (a.map (evalFiber T blk i)) (S.toFibers T blk x i) =
        S.charOnPlaces (placeFiber T blk i) (evalFiber T blk i (a⁻¹.val * simpleRootSum u)) := by
      have h_level : (S.toFibers T blk u i)⁻¹ * S.toFibers T blk x i ∈
          unitaryLevel integers (a.map (evalFiber T blk i))
            (S.latticeMiddle (LocProd (placeFiber T blk i))).splitGram := by
        simpa using (mem_unitaryLevel_iff_toFibers blk).1 hux i
      rw [extendedBesselChar_eq ((mem_besselU_iff_toFibers blk).1 hu i) h_level, hψ']
      simp only [simpleRootSum, map_mul, map_sum, toFibers_apply, Units.coe_map_inv,
        MonoidHom.coe_ofClass]
    rw [extendedBesselChar_eq hu hux, hψ, charOnPlaces_eq_prod_fibers blk]
    simp only [h_fiber]
  · -- If no factor vanished, the unipotent elements of the fibres would glue to one over `T`.
    have h_zero : extendedBesselChar a x = 0 := by
      by_contra h_ne
      exact hx (exists_besselU_of_extendedBesselChar_ne_zero h_ne)
    rw [h_zero, eq_comm, prod_eq_zero_iff]
    contrapose! hx
    have h_fiber (i : ι) : ∃ u ∈ besselU, u⁻¹ * S.toFibers T blk x i ∈
        unitaryLevel integers (a.map (evalFiber T blk i))
          (S.latticeMiddle (LocProd (placeFiber T blk i))).splitGram :=
      exists_besselU_of_extendedBesselChar_ne_zero (hx i (mem_univ i))
    choose u hu hux using h_fiber
    -- The elements `u i` of the fibres are the components of one element `v` over `T`.
    obtain ⟨(v : (S.latticeMiddle (LocProd T)).G), rfl⟩ := toFibers_surjective blk u
    have h_level : v⁻¹ * x ∈ unitaryLevel integers a (S.latticeMiddle (LocProd T)).splitGram :=
      (mem_unitaryLevel_iff_toFibers blk).2 fun i ↦ by simpa using hux i
    exact ⟨v, (mem_besselU_iff_toFibers blk).2 hu, h_level⟩

variable {F' : ∀ i : ι, PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13)))
  (S.latticeMiddle (LocProd (placeFiber T blk i))) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)}

omit [Fintype ι] in
/-- Let `F` be a filling datum at `T` and `F' i` a filling datum at each fibre of a map `blk` on
places. Then the modulus `(F' i).levelUnit` is the projection of the modulus `F.levelUnit` to the
fibre. -/
lemma IsFillingData.levelUnit_eq_map_evalFiber (h : S.IsFillingData T F)
    (h' : ∀ i : ι, S.IsFillingData (placeFiber T blk i) (F' i)) (i : ι) :
    (F' i).levelUnit = F.levelUnit.map (evalFiber T blk i) := by
  rw [h.levelUnit_eq, (h' i).levelUnit_eq]
  rfl

/-- Let `F` be a filling datum at `T` and `F' i` a filling datum at each fibre `placeFiber T blk i`
of a map `blk` from the places to a finite type `ι`. Then there is a constant `t` with the following
property. For all subgroups `Y i` of the unitary groups over the fibres, let `Z` be their product,
read in the group over `T` through `S.toFibers`. Then the volume `F.groupMeasure Z` is `t` times the
product of the volumes `(F' i).groupMeasure (Y i)`. The mass integral, `F.massIntegral Z` = ∫
|∫_Z χ_g(y x y⁻¹) dy|² dx, is `‖t.toReal‖ₑ ^ 2 * t` times the product of the mass integrals of the
`Y i`.

This factor is `t ^ 3` for finite `t`. -/
lemma IsFillingData.exists_massIntegral_pi_eq (h : S.IsFillingData T F)
    (h' : ∀ i : ι, S.IsFillingData (placeFiber T blk i) (F' i)) :
    ∃ t : ℝ≥0∞, ∀ Y : ∀ i : ι, Subgroup (S.latticeMiddle (LocProd (placeFiber T blk i))).G,
      F.massIntegral ((Subgroup.pi .univ Y).comap (S.toFibers T blk)) =
        ‖t.toReal‖ₑ ^ 2 * t * ∏ i : ι, (F' i).massIntegral (Y i) ∧
      F.groupMeasure ((Subgroup.pi .univ Y).comap (S.toFibers T blk)) =
        t * ∏ i : ι, (F' i).groupMeasure (Y i) := by
  have h_emb : MeasurableEmbedding (S.toFibers T blk) := measurableEmbedding_toFibers blk
  -- The image of `F.groupMeasure` is right invariant, so a multiple of the product Haar measure.
  have _ (i : ι) : SigmaFinite (F' i).groupMeasure :=
    (h' i).isHaarMeasure_groupMeasure.sigmaFinite
  have _ : LocallyCompactSpace (∀ i : ι, (S.latticeMiddle (LocProd (placeFiber T blk i))).G) :=
    Pi.locallyCompactSpace_of_finite
  have _ (i : ι) : Nonempty (S.latticeMiddle (LocProd (placeFiber T blk i))).G := ⟨1⟩
  have h_inv : (F.groupMeasure.map (S.toFibers T blk)).IsMulRightInvariant := by
    refine ⟨(toFibers_surjective blk).forall.2 fun x ↦ ?_⟩
    have h_right : MeasurePreserving (· * x) F.groupMeasure F.groupMeasure :=
      measurePreserving_mul_right _ x
    exact ((h_emb.measurable.measurePreserving _).of_semiconj h_right
      (fun y ↦ map_mul (S.toFibers T blk) y x) (by fun_prop)).map_eq
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0∞,
      F.groupMeasure.map (S.toFibers T blk) = t • .pi fun i : ι ↦ (F' i).groupMeasure :=
    exists_eq_smul_haar _ h_inv
  refine ⟨t, fun Y ↦ ⟨?_, ?_⟩⟩
  · -- The inner integral gives the factor `t`: transport along `S.toFibers T blk`, then Fubini.
    have h_phase (y : (S.latticeMiddle (LocProd T)).G) :
        extendedBesselChar F.levelUnit y = ∏ i : ι,
          extendedBesselChar (F' i).levelUnit (S.toFibers T blk y i) := by
      rw [extendedBesselChar_eq_prod_toFibers blk h.psi_eq fun i ↦ (h' i).psi_eq]
      simp only [h.levelUnit_eq_map_evalFiber blk h']
    have h_inner (x : (S.latticeMiddle (LocProd T)).G) :
        ∫ y in (Subgroup.pi .univ Y).comap (S.toFibers T blk),
            extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure =
          t.toReal • ∏ i : ι, ∫ y in Y i,
            extendedBesselChar (F' i).levelUnit (y * S.toFibers T blk x i * y⁻¹)
              ∂(F' i).groupMeasure := by
      rw [← integral_fintype_prod_eq_prod, ← integral_smul_measure, ← Measure.restrict_pi_pi,
        ← Measure.restrict_smul, ← ht, h_emb.setIntegral_map]
      simp [coe_pi, h_phase]
    let f (i : ι) (z : (S.latticeMiddle (LocProd (placeFiber T blk i))).G) : ℝ≥0∞ :=
      ‖∫ y in Y i, extendedBesselChar (F' i).levelUnit (y * z * y⁻¹) ∂(F' i).groupMeasure‖ₑ ^ 2
    -- The outer integral gives one more factor `t`: transport, then Tonelli.
    calc F.massIntegral ((Subgroup.pi .univ Y).comap (S.toFibers T blk))
      _ = ∫⁻ x : (S.latticeMiddle (LocProd T)).G,
          ‖t.toReal‖ₑ ^ 2 * ∏ i : ι, f i (S.toFibers T blk x i) ∂F.groupMeasure := by
        simp only [PlaceData.massIntegral, h_inner, f, mul_pow, prod_pow, enorm, nnnorm_smul,
          nnnorm_prod, ENNReal.coe_mul, ofNNReal_finsetProd]
      _ = ‖t.toReal‖ₑ ^ 2 * ∫⁻ z, ∏ i : ι, f i (z i) ∂F.groupMeasure.map (S.toFibers T blk) := by
        rw [lintegral_const_mul' _ _ (by simp), h_emb.lintegral_map]
      _ = ‖t.toReal‖ₑ ^ 2 * t * ∏ i : ι, (F' i).massIntegral (Y i) := by
        rw [ht, lintegral_smul_measure, lintegral_pi_prod _ (by fun_prop), smul_eq_mul, mul_assoc]
        simp only [PlaceData.massIntegral, f]
  · rw [coe_comap, coe_pi, ← h_emb.map_apply, ht, Measure.smul_apply, Measure.pi_pi, smul_eq_mul]

/-- Let `F` be a filling datum at `T` and `F' i` a filling datum at each fibre of a map `blk` from
the places to a finite type, and let `ϰ` be the mass integral and `vol` the Haar volume. If on each
fibre `ϰ(Y i) vol(W i) c i ≤ ϰ(W i) vol(Y i)`, then the products of the groups, read in the group
over `T` through `S.toFibers`, satisfy `ϰ(∏ Y i) vol(∏ W i) (∏ c i) ≤ ϰ(∏ W i) vol(∏ Y i)`. -/
lemma IsFillingData.massIntegral_pi_mul_le (h : S.IsFillingData T F)
    (h' : ∀ i : ι, S.IsFillingData (placeFiber T blk i) (F' i))
    {Y W : ∀ i : ι, Subgroup (S.latticeMiddle (LocProd (placeFiber T blk i))).G} {c : ι → ℝ≥0∞}
    (h_le : ∀ i : ι, (F' i).massIntegral (Y i) * (F' i).groupMeasure (W i) * c i ≤
      (F' i).massIntegral (W i) * (F' i).groupMeasure (Y i)) :
    F.massIntegral ((Subgroup.pi .univ Y).comap (S.toFibers T blk)) *
          F.groupMeasure ((Subgroup.pi .univ W).comap (S.toFibers T blk)) * ∏ i : ι, c i ≤
      F.massIntegral ((Subgroup.pi .univ W).comap (S.toFibers T blk)) *
        F.groupMeasure ((Subgroup.pi .univ Y).comap (S.toFibers T blk)) := by
  -- Mass integral and volume of a product are products, up to constants that agree on both sides.
  obtain ⟨t, h_prod⟩ : ∃ t : ℝ≥0∞,
      ∀ Z : ∀ i : ι, Subgroup (S.latticeMiddle (LocProd (placeFiber T blk i))).G,
        F.massIntegral ((Subgroup.pi .univ Z).comap (S.toFibers T blk)) =
          ‖t.toReal‖ₑ ^ 2 * t * ∏ i : ι, (F' i).massIntegral (Z i) ∧
        F.groupMeasure ((Subgroup.pi .univ Z).comap (S.toFibers T blk)) =
          t * ∏ i : ι, (F' i).groupMeasure (Z i) :=
    h.exists_massIntegral_pi_eq blk h'
  calc F.massIntegral ((Subgroup.pi .univ Y).comap (S.toFibers T blk)) *
        F.groupMeasure ((Subgroup.pi .univ W).comap (S.toFibers T blk)) * ∏ i : ι, c i
    _ = ‖t.toReal‖ₑ ^ 2 * t * t * ∏ i : ι,
        (F' i).massIntegral (Y i) * (F' i).groupMeasure (W i) * c i := by
      simp only [h_prod, prod_mul_distrib]
      ring
    _ ≤ ‖t.toReal‖ₑ ^ 2 * t * t * ∏ i : ι,
        (F' i).massIntegral (W i) * (F' i).groupMeasure (Y i) := by
      grw [prod_le_prod fun i _ ↦ h_le i]
    _ = F.massIntegral ((Subgroup.pi .univ W).comap (S.toFibers T blk)) *
        F.groupMeasure ((Subgroup.pi .univ Y).comap (S.toFibers T blk)) := by
      simp only [h_prod, prod_mul_distrib]
      ring

end Measures

/-! ### Several places -/

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E]

/-- Let `Sg` be a set of chosen places of the filling `S` above the first level prime. A place `w`
lies in the pair `{s, star s}` for at most one `s` of `Sg`; the index `o` is this `s`, or `none` if
there is none. -/
theorem exists_option_eq_some_iff {S : Filling E 𝔰} (Sg : Finset (S.chosenPlaces 0))
    (w : FinPlace E) :
    ∃ o : Option Sg, ∀ s : Sg, o = some s ↔ w = s ∨ star w = s := by
  by_cases hw : ∃ s : Sg, w = s ∨ star w = s
  · -- The conjugate of a chosen place is not chosen, so `s` is unique.
    obtain ⟨(s : Sg), hs⟩ := hw
    have h_not_conj (a b : S.chosenPlaces 0) : (b : FinPlace E) ≠ star (a : FinPlace E) :=
      ne_of_mem_of_not_mem b.prop (S.star_notMem_chosenPlaces a.prop)
    have h_unique (s' : Sg) (hs' : w = s' ∨ star w = s') : s = s' := by
      have h_place : (s : FinPlace E) = s' := by
        obtain rfl | hs := hs
        · exact hs'.resolve_right (h_not_conj s s').symm
        · obtain rfl | hs' := hs'
          · exact absurd hs.symm (h_not_conj s' s)
          · exact hs.symm.trans hs'
      exact Subtype.ext (Subtype.ext h_place)
    refine ⟨some s, fun s' ↦ ⟨fun h_eq ↦ ?_, fun hs' ↦ congrArg some (h_unique s' hs')⟩⟩
    rwa [← Option.some_injective Sg h_eq]
  · exact ⟨none, by simpa using hw⟩

/-- Let `S` be an admissible filling, `F` a filling datum at `T`, and let the inverse of the level
`S.ideleM` be integral off `T`. Let `Sg` be a set of chosen places above the first level prime
(index `0`) and let `d w = (ε, v)` prescribe, for each such place `w`, the frame vector with nonzero
coordinates `v` modulo `w` if `ε` is false and modulo its conjugate if `ε` is true; `S.fixer Sg d`
is the group that fixes these vectors for all `w` in `Sg`. Then some group `Z` between the
congruence subgroup `F.congruenceSubgroup` and the integral unitary group
`K = unitaryLevel P.integers 1 _` has two properties. (a) `Z` contains the `T`-component of every
integral element `k` whose reduction modulo the chosen places lies in `S.fixer Sg d`. (b) With
`ϰ = F.massIntegral` (the mass integral), `vol = F.groupMeasure` (a Haar measure) and `b = S.b`,
`ϰ(Z) vol(K) (b ^ (6 * 𝔰.k)) ^ #Sg ≤ ϰ(K) vol(Z)`. -/
theorem IsFillingData.exists_intermediateGroup_places [WeilData E] {S : Filling E 𝔰}
    [S.IsAdmissible] {T : Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)]
    {F : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ +
      5)}
    (h : S.IsFillingData T F)
    (Sg : Finset (S.chosenPlaces 0)) (d : ∀ w : S.chosenPlaces 0, S.FrameVector w)
    (hT : (↑S.ideleM⁻¹ : 𝔸f E) ∈ integralOff T) :
    ∃ Z : F.IntermediateGroup,
      -- (a)
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d → S.toPlaces T k ∈ Z.val) ∧
      -- (b)
      F.massIntegral Z *
            F.groupMeasure (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ^ #Sg ≤
        F.massIntegral (unitaryLevel P.integers 1 (S.latticeMiddle (LocProd T)).splitGram) *
          F.groupMeasure Z := by
  classical
  -- Split `T` into the blocks `T ∩ {w, star w}`, `w ∈ Sg`, and the rest;
  -- `IsFillingData.exists_intermediateGroup_one_place` gives a group on each block. The unitary
  -- group over `T` is the product of those over the blocks; take the product group.
  obtain ⟨blk, hblk⟩ : ∃ blk : FinPlace E → Option Sg,
      ∀ (w : FinPlace E) (s : Sg), blk w = some s ↔ w = s ∨ star w = s :=
    Classical.skolem.1 (exists_option_eq_some_iff Sg)
  have h_star (w : FinPlace E) : blk (star w) = blk w :=
    Option.ext fun s ↦ by simp [hblk, or_comm]
  have _ (i : Option Sg) : (placeFiber T blk i).StarStable :=
    ⟨by simp +contextual [fT.out, h_star]⟩
  have h_places (i : Option Sg) :
      ∀ w ∈ i, ∀ j : FinPlace E, j ∈ placeFiber T blk i ↔ j ∈ T ∧ (j = w ∨ star j = w) := by
    rintro w rfl j
    simp [hblk]
  -- A filling datum `F' i` and a group `Z i` on each block.
  have h_levels (i : Option Sg) : ∃ (P' : IntegralPlace (LocProd (placeFiber T blk i)))
      (F' : PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd (placeFiber T blk i)))
        (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)), S.IsFillingData (placeFiber T blk i) F' :=
    S.exists_isFillingData (placeFiber T blk i)
  choose P' F' h' using h_levels
  let K' (i : Option Sg) : Subgroup (S.latticeMiddle (LocProd (placeFiber T blk i))).G :=
    unitaryLevel integers 1 (S.latticeMiddle (LocProd (placeFiber T blk i))).splitGram
  let B : ℝ≥0∞ := ENNReal.ofReal (S.b ^ (6 * 𝔰.k))
  have h_groups (i : Option Sg) : ∃ Z : (F' i).IntermediateGroup,
      (∀ k : S.latticeStabilizer, S.reduction k ∈ S.fixer Sg d →
        S.toPlaces (placeFiber T blk i) k ∈ Z.val) ∧
      (F' i).massIntegral Z * (F' i).groupMeasure (K' i) * i.elim 1 (fun _ ↦ B) ≤
        (F' i).massIntegral (K' i) * (F' i).groupMeasure Z :=
    (h' i).exists_intermediateGroup_one_place Sg i d hT (h_places i)
  choose Z hZ_mem hZ_le using h_groups
  -- `Q Y` is the product of the groups `Y i`, read in the group over `T`.
  let Q (Y : ∀ i : Option Sg, Subgroup (S.latticeMiddle (LocProd (placeFiber T blk i))).G) :
      Subgroup (S.latticeMiddle (LocProd T)).G :=
    (Subgroup.pi .univ Y).comap (S.toFibers T blk)
  have hK : unitaryLevel integers 1 (S.latticeMiddle (LocProd T)).splitGram = Q K' := by
    simp only [Q, K', unitaryLevel_eq_comap_toFibers blk, map_one]
  have h_cong : F.congruenceSubgroup = Q fun i : Option Sg ↦ (F' i).congruenceSubgroup := by
    simp only [Q, PlaceData.congruenceSubgroup, unitaryLevel_eq_comap_toFibers blk,
      h.levelUnit_eq_map_evalFiber blk h']
  have h_between : Q (fun i : Option Sg ↦ Z i) ∈
      Set.Icc F.congruenceSubgroup (unitaryLevel integers 1
        (S.latticeMiddle (LocProd T)).splitGram) := by
    rw [hK, h_cong]
    exact ⟨fun x hx i hi ↦ (Z i).prop.left (hx i hi), fun x hx i hi ↦ (Z i).prop.right (hx i hi)⟩
  refine ⟨⟨Q fun i ↦ Z i, h_between⟩, fun k hk i _ ↦ ?_, ?_⟩
  · rw [toFibers_toPlaces]
    exact hZ_mem i k hk
  -- Multiply the inequalities of the blocks: those of `Sg` give one factor `B` each, the rest `1`.
  have h_gain : ENNReal.ofReal (S.b ^ (6 * 𝔰.k)) ^ #Sg =
      ∏ i : Option Sg, i.elim 1 fun _ ↦ B := by simp [B]
  simp only [hK, h_gain]
  exact h.massIntegral_pi_mul_le blk h' hZ_le

end New.Filling
