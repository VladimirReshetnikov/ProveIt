import OAI.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
import OAI.Combinatorics.Progressions.Geometry.AllocatedLayerQuarterSupport
import OAI.Combinatorics.Progressions.Lattices.PositiveIntegerPeriodization
import OAI.Combinatorics.Progressions.Linear.CanonicalAmbientKernel
import OAI.Combinatorics.Progressions.Probability.LocalLayerOneSiteLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_ambient_torus_fourier_approximation {J : Type*} [Fintype J]
    (f : (J → UnitAddCircle) → ℂ) (L B : ℝ≥0) (hf : LipschitzWith L f)
    (hB : ∀ x, ‖f x‖ ≤ B) {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hJ : (Fintype.card J : ℝ) ≤ P) (hL : (L : ℝ) ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → J → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * B ∧
      ∀ x, ‖f x - ∑ a, c a * ∏ j, CircleFourier.character (frequency a j • x j)‖ ≤ δ := by
  classical
  have hact : ∀ t : J → UnitAddCircle, Isometry (fun x : J → UnitAddCircle => t +ᵥ x) :=
    fun t => isometry_add_left t
  let A := CircleFourier.torusCoordinateAction hact
  have horbit : ∀ i (t : UnitAddCircle) x, dist ((A i).act t x) x ≤ (1 : ℝ≥0) * ‖t‖ := by
    intro i t x
    change dist ((Pi.single i t : J → UnitAddCircle) + x) x ≤ (1 : ℝ) * ‖t‖
    rw [one_mul, dist_eq_norm, add_sub_cancel_right]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg t)).mpr
    intro j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  obtain ⟨F, inst, frequency, v, hcard, hfrequency, hv, hchar, _, herr⟩ :=
    CircleFourier.exists_controlled_commuting_circle_decomposition A
      (CircleFourier.torusCoordinateAction_commutes hact) f L B 1 hf hB horbit δ P hδ hP hJ hL
      (by simpa using Real.one_le_exp hP) hδP
  let _ := inst
  have he (a : F) (x : J → UnitAddCircle) :
      v a x = (∏ j, CircleFourier.character (frequency a j • x j)) * v a 0 := by
    have hc : ∀ i (t : UnitAddCircle) z,
        v a ((Pi.single i t : J → UnitAddCircle) +ᵥ z) = CircleFourier.character (frequency a i • t) * v a z :=
      fun i t z => hchar a i t z
    have hh := CircleFourier.torus_character_of_coordinate_characters (v a) (frequency a) hc x 0
    change v a (x + 0) = _ at hh
    simpa only [add_zero] using hh
  refine ⟨F, inst, frequency, fun a => v a 0, hcard, hfrequency, ?_, ?_⟩
  · calc
      _ ≤ ∑ _a : F, (B : ℝ) := Finset.sum_le_sum (fun a _ => (hv a).2 0)
      _ = (Fintype.card F : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard B.coe_nonneg
  · intro x
    have hs : (∑ a, v a x) = ∑ a, v a 0 * ∏ j, CircleFourier.character (frequency a j • x j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [he a x, mul_comm]
    simpa only [hs, norm_sub_rev] using herr x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_crtProgressionWeight_fourier {J : Type*} [Fintype J]
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → J × Bool → ℤ) (c : F → ℂ),
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
        (z : ZMod (∏ j, N j) × ZMod (∏ j, N j)),
        ‖(crtProgressionWeight N hN k z : ℂ) -
          ∑ a, c a * crtConfigurationCharacter N hN (frequency a) z‖ ≤ δ := by
  let L : ℝ≥0 := ((64 * k : ℕ) : ℝ≥0) / 4
  let f : ((J × Bool) → UnitAddCircle) → ℂ := fun w => (progressionTorusCutoff k w : ℂ)
  have hf : LipschitzWith L f := by
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (progressionTorusCutoff_lipschitz (J := J) k)
  have hB : ∀ w, ‖f w‖ ≤ (1 : ℝ≥0) := by
    intro w
    simpa only [f, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (progressionTorusCutoff_range k w).1, NNReal.coe_one] using
      (progressionTorusCutoff_range k w).2
  let P : ℝ := Fintype.card (J × Bool) + L + δ⁻¹
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hc : (0 : ℝ) ≤ Fintype.card (J × Bool) := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hJ : (Fintype.card (J × Bool) : ℝ) ≤ P := by dsimp [P]; linarith [L.coe_nonneg]
  have hL : (L : ℝ) ≤ Real.exp P := by
    have he := Real.add_one_le_exp P
    dsimp [P] at he
    linarith
  have hδP : δ⁻¹ ≤ Real.exp P := by
    have he := Real.add_one_le_exp P
    dsimp [P] at he
    linarith [L.coe_nonneg]
  obtain ⟨F, inst, frequency, c, _, _, _, happ⟩ :=
    exists_ambient_torus_fourier_approximation f L 1 hf hB hδ hP hJ hL hδP
  refine ⟨F, inst, frequency, c, ?_⟩
  intro N _ hN z
  exact happ (crtConfigurationTorus N hN z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem subspaceAmbientTorus_character {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : J → ℤ) (x : SubspaceArrayTorus Unit U) :
    (∏ j, CircleFourier.character (frequency j • subspaceAmbientTorus U x j)) =
      subspaceArrayCharacter U (Matrix.of (fun (_ : Unit) j => frequency j)) x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) x
  simp only [subspaceAmbientTorus_mk]
  change _ = CircleFourier.character
    ((∑ _u : Unit, ∑ j, (frequency j : ℝ) * (y ()).val j : ℝ) : UnitAddCircle)
  rw [Fintype.sum_unique, character_real_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

theorem exists_subspace_ambient_fourier_approximation {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (f : (J → UnitAddCircle) → ℂ)
    (L B : ℝ≥0) (hf : LipschitzWith L f) (hB : ∀ x, ‖f x‖ ≤ B)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hJ : (Fintype.card J : ℝ) ≤ P)
    (hL : (L : ℝ) ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (A : Type) (inst : Fintype A), letI := inst
    ∃ (frequency : A → J → ℤ) (c : A → ℂ),
      (Fintype.card A : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * B ∧
      ∀ x, ‖f (subspaceAmbientTorus U x) -
        ∑ a, c a * subspaceArrayCharacter U (Matrix.of (fun (_ : Unit) j => frequency a j)) x‖ ≤ δ := by
  obtain ⟨A, inst, frequency, c, hcard, hfreq, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation f L B hf hB hδ hP hJ hL hδP
  let _ := inst
  refine ⟨A, inst, frequency, c, hcard, hfreq, hmass, ?_⟩
  intro x
  simpa only [subspaceAmbientTorus_character] using herr (subspaceAmbientTorus U x)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem exists_local_subspace_fourier_density {J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ))
    [MeasurableSpace (SubspaceArrayTorus Unit U)] [BorelSpace (SubspaceArrayTorus Unit U)]
    (μ : Measure (SubspaceArrayTorus Unit U)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    {q : ℕ} (hq : 16 ≤ q) {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hJ : (Fintype.card J : ℝ) ≤ P) (hqP : (q : ℝ) ^ (Fintype.card J + 1) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ F : (J → UnitAddCircle) → ℝ,
      (∀ z, 0 ≤ F z ∧ F z ≤ 2 * (q : ℝ) ^ Fintype.card J) ∧
      LipschitzWith ((q : ℝ≥0) ^ (Fintype.card J + 1)) F ∧
      ∀ center : SubspaceArrayTorus Unit U,
        Integrable (fun x => F (subspaceAmbientTorus U (x - center))) μ ∧
        (∫ x, F (subspaceAmbientTorus U (x - center)) ∂μ) = 1 ∧
        (∀ x, F (subspaceAmbientTorus U (x - center)) ≠ 0 →
          ∃ y : J → ℝ, ∀ j, (y j : UnitAddCircle) = subspaceAmbientTorus U (x - center) j ∧
            |y j| < 4 / (q : ℝ) ∧ |y j| < 1 / 4) ∧
        ∃ (A : Type) (inst : Fintype A), letI := inst
        ∃ (frequency : A → J → ℤ) (c : A → ℂ),
          (Fintype.card A : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
          (∀ a j, |(frequency a j : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
          (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
            (2 * (q : ℝ) ^ Fintype.card J) ∧
          ∀ x, ‖(F (subspaceAmbientTorus U (x - center)) : ℂ) -
            ∑ a, c a * subspaceArrayCharacter U (Matrix.of (fun (_ : Unit) j => frequency a j)) x‖ ≤ δ := by
  obtain ⟨F, hF, hLip, hlocal⟩ := exists_local_subspace_density U μ hq
  refine ⟨F, hF, hLip, ?_⟩
  intro center
  obtain ⟨hi, hm, hs⟩ := hlocal center
  refine ⟨hi, hm, hs, ?_⟩
  let g : (J → UnitAddCircle) → ℂ := fun z => (F (z - subspaceAmbientTorus U center) : ℂ)
  have hg : LipschitzWith ((q : ℝ≥0) ^ (Fintype.card J + 1)) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (Complex.ofReal (F (x - subspaceAmbientTorus U center)))
      (Complex.ofReal (F (y - subspaceAmbientTorus U center))) ≤ _
    rw [Complex.isometry_ofReal.dist_eq]
    simpa only [dist_sub_right] using
      hLip.dist_le_mul (x - subspaceAmbientTorus U center) (y - subspaceAmbientTorus U center)
  have hb : ∀ z, ‖g z‖ ≤ (2 * (q : ℝ≥0) ^ Fintype.card J : ℝ≥0) := by
    intro z
    change ‖(F (z - subspaceAmbientTorus U center) : ℂ)‖ ≤ _
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF _).1,
      NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_natCast] using
      (hF (z - subspaceAmbientTorus U center)).2
  obtain ⟨A, inst, frequency, c, hcard, hfreq, hmass, herr⟩ :=
    exists_subspace_ambient_fourier_approximation U g _ _ hg hb hδ hP hJ
      (by simpa only [NNReal.coe_pow, NNReal.coe_natCast] using hqP) hδP
  let _ := inst
  refine ⟨A, inst, frequency, c, hcard, hfreq, ?_, ?_⟩
  · simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_natCast] using hmass
  · intro x
    simpa only [g, map_sub] using herr x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

noncomputable def smallBoxTorusKernel (H : (D → ℝ) → ℝ) : (D → UnitAddCircle) → ℝ :=
  realPeriodicTorusLift (positiveIntegerPeriodization H)

omit [Fintype D] in
theorem smallBoxTorusKernel_local (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ)
    (hx : ∀ i, |x i| < 1/2) :
    smallBoxTorusKernel H (fun i => (x i : UnitAddCircle)) = H x := by
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  exact positiveIntegerPeriodization_local H hs x hx

theorem smallBoxTorusKernel_lipschitz (H : (D → ℝ) → ℝ) {L : ℝ≥0}
    (hL : LipschitzWith L H) (h0 : ∀ x, 0 ≤ H x)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (smallBoxTorusKernel H) :=
  realPeriodicTorusLift_lipschitz _ (positiveIntegerPeriodization_lipschitz H hL h0 hs)
    (positiveIntegerPeriodization_periodic H)

omit [Fintype D] in
theorem smallBoxTorusKernel_range (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → UnitAddCircle) :
    0 ≤ smallBoxTorusKernel H x ∧ smallBoxTorusKernel H x ≤ B :=
  realPeriodicTorusLift_range _ (positiveIntegerPeriodization_range H hB hH hs) x

theorem exists_small_box_fourier_approximation
    (H : (D → ℝ) → ℝ) (L B : ℝ≥0) (hL : LipschitzWith L H)
    (hB : ∀ x, 0 ≤ H x ∧ H x ≤ B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hD : (Fintype.card D : ℝ) ≤ P)
    (hLP : (L : ℝ) ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → D → ℤ) (c : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ a i, |(frequency a i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ a, ‖c a‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * B ∧
      ∀ (x : D → ℝ), (∀ i, |x i| < 1/2) →
        ‖(H x : ℂ) - ∑ a, c a * ∏ i,
          CircleFourier.character (frequency a i • (x i : UnitAddCircle))‖ ≤ δ := by
  have hl : LipschitzWith L (fun x => (smallBoxTorusKernel H x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact (smallBoxTorusKernel_lipschitz H hL (fun x => (hB x).1) hs).dist_le_mul x y
  have hb (x : D → UnitAddCircle) : ‖(smallBoxTorusKernel H x : ℂ)‖ ≤ B := by
    obtain ⟨h0, hcap⟩ := smallBoxTorusKernel_range H B.coe_nonneg hB hs x
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using hcap
  obtain ⟨F, inst, frequency, c, hcard, hfreq, hsum, herr⟩ :=
    exists_ambient_torus_fourier_approximation _ L B hl hb hδ hP hD hLP hδP
  let _ := inst
  refine ⟨F, inst, frequency, c, hcard, hfreq, hsum, ?_⟩
  intro x hx
  simpa only [smallBoxTorusKernel_local H hs x hx] using herr (fun i => (x i : UnitAddCircle))

end Erdos3

end

section

namespace Erdos3
open scoped Classical

variable {D : Type*} [Fintype D]

omit [Fintype D] in
theorem smallBoxTorusKernel_nonzero_quarter_lift [Fintype D] (H : (D → ℝ) → ℝ)
    (hs : ∀ v, H v ≠ 0 → ∀ i, |v i| ≤ 1 / 4)
    (x : D → UnitAddCircle) (hx : smallBoxTorusKernel H x ≠ 0) :
    ∃ v : D → ℝ, (∀ i, |v i| ≤ 1 / 4) ∧
      (fun i => (v i : UnitAddCircle)) = x ∧ H v = smallBoxTorusKernel H x := by
  let a : D → ℝ := fun i => (AddCircle.equivIoc 1 0 (x i)).val
  have hn : ∃ n : D → ℤ, H (fun i => a i + (n i : ℝ)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    change (∑' n : D → ℤ, H (fun i => a i + (n i : ℝ))) = 0
    simp only [h, tsum_zero]
  obtain ⟨n, hn⟩ := hn
  let v : D → ℝ := fun i => a i + (n i : ℝ)
  have hv : ∀ i, |v i| ≤ 1 / 4 := hs v hn
  have hcoe : (fun i => (v i : UnitAddCircle)) = x := by
    funext i
    simp [v, a]
  refine ⟨v, hv, hcoe, ?_⟩
  rw [← hcoe]
  symm
  apply smallBoxTorusKernel_local H
  · intro z hz i
    exact (hs z hz i).trans_lt (by norm_num)
  · intro i
    exact (hv i).trans_lt (by norm_num)

theorem smallBoxTorusKernel_zero_outside_quarter (H : (D → ℝ) → ℝ)
    (hs : ∀ v, H v ≠ 0 → ∀ i, |v i| ≤ 1 / 4)
    (x : D → UnitAddCircle) (hx : ∃ i, 1 / 4 < ‖x i‖) : smallBoxTorusKernel H x = 0 := by
  by_contra hn
  obtain ⟨v, hv, he, _⟩ := smallBoxTorusKernel_nonzero_quarter_lift H hs x hn
  obtain ⟨i, hi⟩ := hx
  rw [← he] at hi
  rw [norm_eq_abs_centeredCircleLift, centeredCircleLift_coe (hv i)] at hi
  exact (not_lt_of_ge (hv i)) hi

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem coordinate_integer_translate_sub_mem (u : EuclideanSpace ℝ D) (z : D → ℤ) :
    u - (EuclideanSpace.equiv D ℝ).symm (fun i => u i + (z i : ℝ)) ∈
      standardEuclideanLattice D := by
  apply (mem_standardEuclideanLattice D _).mpr
  intro i
  refine ⟨-z i, ?_⟩
  change ((-z i : ℤ) : ℝ) = u i - (u i + (z i : ℝ))
  push_cast
  ring

theorem exists_coordinate_integer_translate (u v : EuclideanSpace ℝ D)
    (hv : u - v ∈ standardEuclideanLattice D) :
    ∃ z : D → ℤ, (fun i => v i) = fun i => u i + (z i : ℝ) := by
  choose z hz using (mem_standardEuclideanLattice D _).mp hv
  refine ⟨fun i => -z i, ?_⟩
  funext i
  have hi : (z i : ℝ) = u i - v i := hz i
  push_cast
  linarith

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalAmbientTorusDensity (c w : I → ℝ) (f : Fin n → ℝ → ℝ) :
    (D → UnitAddCircle) → ℝ :=
  smallBoxTorusKernel (canonicalAmbientKernel W b o c w f)

theorem canonicalAmbientTorusDensity_eq (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    (u : W) :
    canonicalAmbientTorusDensity W b o c w f (fun i => (u.val i : UnitAddCircle)) =
      canonicalMixedDensity W b hb o c w p
        (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) := by
  let H := canonicalAmbientKernel W b o c w f
  let d := canonicalMixedDensity W b hb o c w p
    (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u)
  have hsupport : ∀ v, H v ≠ 0 → ∀ i, |v i| < 1/2 :=
    canonicalAmbientKernel_support W b o c w f
  have hlocal (v : D → ℝ)
      (hv : u.val - (EuclideanSpace.equiv D ℝ).symm v ∈ standardEuclideanLattice D)
      (hvsmall : ∀ i, |v i| < 1/2) : H v = d :=
    canonicalAmbientKernel_eq_of_lift W b hb o c w f p hf hs u v hv hvsmall
  change realPeriodicTorusLift (positiveIntegerPeriodization H)
    (fun i => (u.val i : UnitAddCircle)) = d
  rw [realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  by_cases hd : d = 0
  · rw [hd]
    have hz : ∀ z : D → ℤ, H (fun i => u.val i + (z i : ℝ)) = 0 := by
      intro z
      by_cases hz : H (fun i => u.val i + (z i : ℝ)) = 0
      · exact hz
      · exact (hlocal _ (coordinate_integer_translate_sub_mem u.val z) (hsupport _ hz)).trans hd
    simp only [positiveIntegerPeriodization, hz, tsum_zero]
  · obtain ⟨x, hxsmall, hq, _⟩ := canonicalMixedDensity_recover W b hb o c w p hd
    let v := normalizedLatticePoint W b (orthonormalMixedChart o x)
    have hv : u.val - v ∈ standardEuclideanLattice D :=
      normalizedLatticePoint_sub_mem_of_mk_eq W b hb u _ hq.symm
    obtain ⟨z, hz⟩ := exists_coordinate_integer_translate u.val v hv
    calc
      positiveIntegerPeriodization H (fun i => u.val i) =
          positiveIntegerPeriodization H (fun i => v i) := by
        rw [hz]
        exact (positiveIntegerPeriodization_periodic H _ z).symm
      _ = H (fun i => v i) := positiveIntegerPeriodization_local H hsupport _ hxsmall
      _ = d := hlocal _ hv hxsmall

theorem canonicalAmbientTorusDensity_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ canonicalAmbientTorusDensity W b o c w f x ∧
      canonicalAmbientTorusDensity W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (canonicalAmbientTorusDensity W b o c w f) := by
  obtain ⟨hcap, hlip⟩ := canonicalAmbientKernel_bounds W b o c w f hM hJ hC hV
  exact ⟨smallBoxTorusKernel_range _ (mul_nonneg V.coe_nonneg M.coe_nonneg) hcap
      (canonicalAmbientKernel_support W b o c w f),
    smallBoxTorusKernel_lipschitz _ hlip (fun x => (hcap x).1)
      (canonicalAmbientKernel_support W b o c w f)⟩

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

theorem canonicalAmbientTorusDensity_eq_of_support_bounds
    (c w : I → ℝ) (f : Fin n → ℝ → ℝ) (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ x, ‖(normalizedOrthogonalChart W b).symm x‖ ≤ C * ‖x‖)
    (hsmall : C * ((Fintype.card I : ℝ) + 1) * R ≤ 1/4)
    (hw : ∀ i, 0 < w i) (hcw : ∀ i, |c i| + w i ≤ R)
    (hp : ∀ i k, k ∈ (p i).support → |(k : ℝ) / basisAxisScale b i| ≤ R) (u : W) :
    canonicalAmbientTorusDensity W b o c w f (fun i => (u.val i : UnitAddCircle)) =
      canonicalMixedDensity W b hb o c w p
        (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) :=
  canonicalAmbientTorusDensity_eq W b hb o c w f p hf
    (mixedCoefficient_quarter_support W b o hC hR hchart hsmall c w hw hcw p hp) u

theorem exists_canonical_density_fourier_approximation
    (c w : I → ℝ) (f : Fin n → ℝ → ℝ) (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P) (hD : (Fintype.card D : ℝ) ≤ P)
    (hLP : ((V * (J * (C * Fintype.card D)) + (V * M) * 8 : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → D → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t i, |(frequency t i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * (V * M) ∧
      ∀ u : W, ‖(canonicalMixedDensity W b hb o c w p
          (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) : ℂ) -
        ∑ t, a t * ∏ i, CircleFourier.character (frequency t i • (u.val i : UnitAddCircle))‖ ≤ δ := by
  obtain ⟨hcap, hlip⟩ := canonicalAmbientTorusDensity_bounds W b o c w f hM hJ hC hV
  have hc : LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (fun x => (canonicalAmbientTorusDensity W b o c w f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hlip.dist_le_mul x y
  have hbnd (x) : ‖(canonicalAmbientTorusDensity W b o c w f x : ℂ)‖ ≤ (V * M : ℝ≥0) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcap x).1, NNReal.coe_mul]
      using (hcap x).2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_ambient_torus_fourier_approximation _ _ (V * M) hc hbnd hδ hP hD hLP hδP
  let _ := inst
  refine ⟨F, inst, frequency, a, hcard, hfreq, hsum, ?_⟩
  intro u
  simpa only [canonicalAmbientTorusDensity_eq W b hb o c w f p hf hs u] using
    herr (fun i => (u.val i : UnitAddCircle))

end Erdos3

end

end OAI
