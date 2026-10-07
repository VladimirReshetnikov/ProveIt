/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {I : A → Type*} [∀ a, Fintype (I a)]

theorem sigma_sum_coefficient_norm_le (w : A → ℂ) (c : ∀ a, I a → ℂ)
    {C B : ℝ} (hB : 0 ≤ B) (hw : (∑ a, ‖w a‖) ≤ C)
    (hc : ∀ a, (∑ i, ‖c a i‖) ≤ B) :
    (∑ p : Σ a, I a, ‖w p.1 * c p.1 p.2‖) ≤ C * B := by
  rw [Fintype.sum_sigma]
  simp only [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ a, ‖w a‖ * B :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hc a) (norm_nonneg _))
    _ = (∑ a, ‖w a‖) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ C * B := mul_le_mul_of_nonneg_right hw hB

theorem sigma_sum_approximation_error (w g : A → ℂ) (c v : ∀ a, I a → ℂ)
    {C ε : ℝ} (hε : 0 ≤ ε) (hw : (∑ a, ‖w a‖) ≤ C)
    (he : ∀ a, ‖g a - ∑ i, c a i * v a i‖ ≤ ε) :
    ‖(∑ a, w a * g a) -
      ∑ p : Σ a, I a, (w p.1 * c p.1 p.2) * v p.1 p.2‖ ≤ C * ε := by
  rw [Fintype.sum_sigma]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, ‖w a * g a - w a * ∑ i, c a i * v a i‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖w a‖ * ε := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (he a) (norm_nonneg _)
    _ = (∑ a, ‖w a‖) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ C * ε := mul_le_mul_of_nonneg_right hw hε

theorem sigma_partition_card_le {S : Type*} [Fintype S] [DecidableEq S]
    (n : A → ℕ) {B : ℝ} (hn : ∀ a, (n a : ℝ) ≤ B) :
    (Fintype.card (Σ a, S → Fin (n a)) : ℝ) ≤ Fintype.card A * B ^ Fintype.card S := by
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Nat.cast_sum, Nat.cast_pow]
  calc
    _ ≤ ∑ _a : A, B ^ Fintype.card S := by
      apply Finset.sum_le_sum
      intro a _
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hn a) _
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {T K L S U : Type*} [Fintype T] [Fintype K] [Fintype L] [Fintype S]
variable (c : T → ℂ) (a : K → L → ℂ)
variable (g : T → S → U → ℂ) (f : K → L → S → U → ℂ) (v : S → U)

theorem finiteSitePrefactor_substitution_identity :
    (∑ t, c t * ((∑ k, ∑ l, a k l * ∏ s, f k l s (v s)) * ∏ s, g t s (v s))) =
      ∑ t, ∑ k, ∑ l, (c t * a k l) * ∏ s, g t s (v s) * f k l s (v s) := by
  simp only [Finset.prod_mul_distrib, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem finiteSitePrefactor_substitution_error (P : ℂ) {ε : ℝ}
    (hg : ∀ t s u, ‖g t s u‖ ≤ 1)
    (he : ‖P - ∑ k, ∑ l, a k l * ∏ s, f k l s (v s)‖ ≤ ε) :
    ‖(∑ t, c t * (P * ∏ s, g t s (v s))) -
      ∑ t, ∑ k, ∑ l, (c t * a k l) * ∏ s, g t s (v s) * f k l s (v s)‖ ≤
        (∑ t, ‖c t‖) * ε := by
  rw [← finiteSitePrefactor_substitution_identity c a g f v, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ t, ‖c t‖ * ε := by
      apply Finset.sum_le_sum
      intro t _
      rw [← mul_sub, ← sub_mul, norm_mul, norm_mul]
      have hp : ‖∏ s, g t s (v s)‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun s _ => hg t s (v s))
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa using he)) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem finiteSitePrefactor_coefficient_mass :
    (∑ t, ∑ k, ∑ l, ‖c t * a k l‖) = (∑ t, ‖c t‖) * ∑ k, ∑ l, ‖a k l‖ := by
  simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

noncomputable def weightedPlateauModeCoefficient (K M : ℕ) (rows : Finset (Finset I))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card *
    ∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k

omit [NeZero M] in
theorem weightedPlateauModeCoefficient_sum_le (rows : Finset (Finset I))
    (F : Finset (rows → Fin M)) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ C) :
    (∑ k : F, ‖weightedPlateauModeCoefficient c s offset K M rows k‖) ≤ C := by
  rw [← Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun k => ‖weightedPlateauModeCoefficient c s offset K M rows k‖)]
  simp only [weightedPlateauModeCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, ← Finset.mul_sum]
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  apply (mul_le_mul_of_nonneg_left
    ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans hcap) (by positivity)).trans
  exact mul_le_of_le_one_left hC hscale

noncomputable def weightedPlateauModeModel (p : PMF T) (H : ℝ) (K : ℕ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (shift : T → rows → ℤ) (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) : ℂ :=
  finiteResidueModeModel (fun k : F => D k) (fun k => a k)
    (fun k => weightedPlateauModeCoefficient c s offset K M rows k)
    (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift) residue x

omit [NeZero M] [Countable T] [MeasurableSingletonClass T] in
theorem weightedPlateauModeModel_norm (p : PMF T) (H : ℝ) (rows : Finset (Finset I))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ C)
    (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) :
    ‖weightedPlateauModeModel c s offset p H K rows F D a ω shift residue x‖ ≤ C := by
  unfold weightedPlateauModeModel
  exact finiteResidueModeModel_norm (fun k : F => D k) (fun k => a k)
    (fun k => weightedPlateauModeCoefficient c s offset K M rows k)
    (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift)
    (weightedPlateauModeCoefficient_sum_le c s offset rows F hscale hcap)
    (fun k y => plateauModeMixture_norm p H (D k) K (a k) (ω k) shift y) residue x

omit [NeZero M] in
theorem weightedPlateauModeModel_lipschitz (p : PMF T) (H : ℝ) (rows : Finset (Finset I))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) (C W : ℝ≥0)
    (hcap : (∑ k, ‖∏ b, weightedModerateGridCoefficient (c b) (s b) (offset b : ℝ) M rows k‖) ≤ C)
    (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W) (residue : ∀ k : F, rows → ZMod (D k)) :
    LipschitzWith (C * (CircleFourier.characterLipConstant * (rows.card * W) + 4))
      (weightedPlateauModeModel c s offset p H K rows F D a ω shift residue) := by
  unfold weightedPlateauModeModel
  have h := finiteResidueModeModel_lipschitz (fun k : F => D k) (fun k => a k)
    (fun k => weightedPlateauModeCoefficient c s offset K M rows k)
    (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift) C
    (CircleFourier.characterLipConstant * (Fintype.card rows * W) + 4)
    (weightedPlateauModeCoefficient_sum_le c s offset rows F hscale hcap)
    (fun k => plateauModeMixture_lipschitz p H (D k) K (a k) (ω k) shift W (hW k k.property)) residue
  simpa only [Fintype.card_coe] using h

theorem weightedPlateauModeModel_grid_value (p : PMF T) (hK : 0 < K) (H : ℝ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (z : rows → ℤ) :
    (∫ v, weightedModeratePlateauApproximation c s offset K H rows (shift v) z F ∂p.toMeasure) =
      weightedPlateauModeModel c s offset p H K rows F D a ω shift
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / K) := by
  rw [weightedModeratePlateauMixture_expansion c s offset p hK H rows shift z F D a ω hfreq]
  let term (k : rows → Fin M) := weightedPlateauModeCoefficient c s offset K M rows k *
    (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
      plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K))
  calc
    _ = ∑ k ∈ F, term k := by
      simp only [term, weightedPlateauModeCoefficient, Finset.mul_sum, mul_assoc]
    _ = ∑ k : F, term k := Finset.sum_subtype F (fun _ => Iff.rfl) term
    _ = _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

noncomputable def selectedBooleanSiteRows (axis : A) (rows : Finset (Finset α))
    (x : Finset α → A → ℝ) : rows → ℝ :=
  fun t => booleanCoefficient (fun s => x s axis) t

omit [DecidableEq A] in
theorem selectedBooleanSiteRows_lipschitz (axis : A) (rows : Finset (Finset α)) :
    LipschitzWith ((2 : ℝ≥0) ^ Fintype.card α) (selectedBooleanSiteRows axis rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  change |booleanCoefficient (fun s => x s axis) t - booleanCoefficient (fun s => y s axis) t| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s axis - y s axis| ≤ dist (x s) (y s) from
      dist_le_pi_dist (x s) (y s) axis).trans (dist_le_pi_dist x y s)

omit [Fintype α] [Fintype A] [DecidableEq A] in
theorem selectedBooleanSiteRows_integer (axis : A) (rows : Finset (Finset α))
    (N : A → ℕ) (y : Finset α → A → ℤ) :
    selectedBooleanSiteRows axis rows (fun s d => (y s d : ℝ) / N d) =
      fun t : rows => ((booleanCoefficient (fun s => y s axis) t : ℤ) : ℝ) / N axis := by
  funext t
  rw [selectedBooleanSiteRows, booleanCoefficient_div]
  congr 1
  exact (booleanCoefficient_map (Int.castRingHom ℝ) (fun s => y s axis) t).symm

noncomputable def rationalBooleanSitePhase (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (s : Finset α) (v : ZMod D) : ℂ :=
  rationalGridPhase D a (fun t => booleanCoefficient (Pi.single s v) t)

omit [Fintype α] in
theorem rationalBooleanSitePhase_norm (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (s : Finset α) (v : ZMod D) :
    ‖rationalBooleanSitePhase D rows a s v‖ = 1 := rationalGridPhase_norm _ _ _

theorem rationalBooleanSitePhase_prod (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (r : Finset α → ZMod D) :
    rationalGridPhase D a (fun t => booleanCoefficient r t) =
      ∏ s, rationalBooleanSitePhase D rows a s (r s) := by
  have hsum (t : rows) : booleanCoefficient r t =
      ∑ s : Finset α, booleanCoefficient (Pi.single s (r s)) t := by
    rw [← booleanCoefficient_sum]
    congr 1
    funext u
    simp [Pi.single_apply]
  unfold rationalBooleanSitePhase rationalGridPhase
  simp_rw [hsum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, map_sum, CircleFourier.character_fintype_sum]

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_plateau_mode_site_approximation (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (axis : A) (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × A → Fin n) → ℂ)
        (f : (Finset α × A → Fin n) → Finset α → (A → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card A : ℕ) * (4 * P + 8) + P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card A + 6 * P + 12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset α → A → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖plateauModeMixture p H D K a ω shift (selectedBooleanSiteRows axis rows x) -
            ∑ k, c k * ∏ s, f k s (x s)‖ ≤ ε := by
  apply exists_grouped_site_approximation _ 1
    ((CircleFourier.characterLipConstant * (rows.card * W) + 4) * (2 : ℝ≥0) ^ Fintype.card α)
    (fun x => plateauModeMixture_norm p H D K a ω shift _) _ hR hε hP hRP
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hP) hLP hεP
  have h := (plateauModeMixture_lipschitz p H D K a ω shift W hW).comp
    (selectedBooleanSiteRows_lipschitz axis rows)
  simpa only [Fintype.card_coe, Function.comp_def] using h

theorem exists_residue_plateau_site_approximation (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (axis : A) (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × A → Fin n) → ℂ)
        (f : (Finset α × A → Fin n) → Finset α → ZMod D → (A → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card A : ℕ) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (Fintype.card A + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ (r : Finset α → ZMod D) (x : Finset α → A → ℝ), (∀ s d, |x s d| ≤ R) →
          ‖star (rationalGridPhase D a (fun t => booleanCoefficient r t)) *
              plateauModeMixture p H D K a ω shift (selectedBooleanSiteRows axis rows x) -
            ∑ k, c k * ∏ s, f k s (r s) (x s)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ :=
    exists_plateau_mode_site_approximation p H D K axis rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, (fun k s r x => star (rationalBooleanSitePhase D rows a s r) * f k s x),
    hc, ?_, ?_, ?_⟩
  · intro k s r x
    rw [norm_mul, norm_star, rationalBooleanSitePhase_norm, one_mul]
    exact hf k s x
  · intro k s r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← mul_sub, norm_mul, norm_star, rationalBooleanSitePhase_norm, one_mul]
    simpa only [dist_eq_norm] using (hLf k s).dist_le_mul x y
  · intro r x hx
    have hp : (∏ s, star (rationalBooleanSitePhase D rows a s (r s))) =
        star (rationalGridPhase D a (fun t => booleanCoefficient r t)) := by
      rw [← star_prod, ← rationalBooleanSitePhase_prod]
    have hs : (∑ k, c k * ∏ s, star (rationalBooleanSitePhase D rows a s (r s)) * f k s (x s)) =
        star (rationalGridPhase D a (fun t => booleanCoefficient r t)) *
          ∑ k, c k * ∏ s, f k s (x s) := by
      simp only [Finset.prod_mul_distrib, hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs, ← mul_sub, norm_mul, norm_star, rationalGridPhase_norm, one_mul]
    exact he x hx

theorem exists_integer_plateau_site_approximation (p : PMF T) (H : ℝ) (D : ℕ) [NeZero D]
    (axis : A) (N : A → ℕ) (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × A → Fin n) → ℂ)
        (f : (Finset α × A → Fin n) → Finset α → ZMod D → (A → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card A : ℕ) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (Fintype.card A + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ y : Finset α → A → ℤ, (∀ s d, |(y s d : ℝ) / N d| ≤ R) →
          ‖star (rationalGridPhase D a (integerGridResidue D
                (fun t => booleanCoefficient (fun s => y s axis) t))) *
              plateauModeMixture p H D (N axis) a ω shift
                (fun t => ((booleanCoefficient (fun s => y s axis) t : ℤ) : ℝ) / N axis) -
            ∑ k, c k * ∏ s, f k s (y s axis : ZMod D) (fun d => (y s d : ℝ) / N d)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ := exists_residue_plateau_site_approximation
    p H D (N axis) axis rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, f, hc, hf, hLf, ?_⟩
  intro y hy
  have hb := he (fun s => (y s axis : ZMod D)) (fun s d => (y s d : ℝ) / N d) hy
  rw [selectedBooleanSiteRows_integer] at hb
  have hcast : (fun t : rows => booleanCoefficient (fun s => (y s axis : ZMod D)) t) =
      integerGridResidue D (fun t : rows => booleanCoefficient (fun s => y s axis) t) := by
    funext t
    exact (booleanCoefficient_map (Int.castRingHom (ZMod D)) (fun s => y s axis) t).symm
  rw [hcast] at hb
  exact hb

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α T : Type*} [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_scalar_residue_plateau_site_approximation
    (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × Unit → Fin n) → ℂ)
        (f : (Finset α × Unit → Fin n) → Finset α → ZMod D → ℝ → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ (r : Finset α → ZMod D) (x : Finset α → ℝ), (∀ s, |x s| ≤ R) →
          ‖star (rationalGridPhase D a (fun t => booleanCoefficient r t)) *
              plateauModeMixture p H D K a ω shift (fun t => booleanCoefficient x t) -
            ∑ k, c k * ∏ s, f k s (r s) (x s)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ :=
    exists_residue_plateau_site_approximation p H D K () rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, (fun k s r x => f k s r (fun _ => x)), ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_unit, mul_one] using hc
  · intro k s r x
    exact hf k s r _
  · intro k s r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Fintype.card_unit, Nat.cast_one, dist_pi_const] using
      (hLf k s r).dist_le_mul (fun _ => x) (fun _ => y)
  · intro r x hx
    exact he r (fun s _ => x s) (fun s _ => hx s)

theorem exists_scalar_integer_plateau_site_approximation
    (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × Unit → Fin n) → ℂ)
        (f : (Finset α × Unit → Fin n) → Finset α → ZMod D → ℝ → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ y : Finset α → ℤ, (∀ s, |(y s : ℝ) / K| ≤ R) →
          ‖star (rationalGridPhase D a (integerGridResidue D
                (fun t => booleanCoefficient y t))) *
              plateauModeMixture p H D K a ω shift
                (fun t => ((booleanCoefficient y t : ℤ) : ℝ) / K) -
            ∑ k, c k * ∏ s, f k s (y s : ZMod D) ((y s : ℝ) / K)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ := exists_scalar_residue_plateau_site_approximation
    p H D K rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, f, hc, hf, hLf, ?_⟩
  intro y hy
  have h := he (fun s => (y s : ZMod D)) (fun s => (y s : ℝ) / K) hy
  have hr : (fun t : rows => booleanCoefficient (fun s => (y s : ZMod D)) t) =
      integerGridResidue D (fun t : rows => booleanCoefficient y t) := by
    funext t
    exact (booleanCoefficient_map (Int.castRingHom (ZMod D)) y t).symm
  have hx : (fun t : rows => booleanCoefficient (fun s => (y s : ℝ) / K) t) =
      (fun t : rows => ((booleanCoefficient y t : ℤ) : ℝ) / K) := by
    funext t
    rw [booleanCoefficient_div]
    congr 1
    exact (booleanCoefficient_map (Int.castRingHom ℝ) y t).symm
  rwa [hr, hx] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

abbrev PlateauSiteIndex (α A : Type*) (n : A → ℕ) :=
  Σ a, (Finset α × Unit → Fin (n a))

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A]

theorem plateauSiteIndex_card_le (n : A → ℕ) {P : ℝ}
    (hn : ∀ m, (n m : ℝ) ≤ Real.exp (4 * P + 8)) :
    (Fintype.card (PlateauSiteIndex α A n) : ℝ) ≤
      Fintype.card A * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) := by
  have hb := sigma_partition_card_le (A := A) (S := Finset α × Unit) n hn
  rw [Fintype.card_prod, Fintype.card_unit, mul_one, ← Real.exp_nat_mul] at hb
  exact hb

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_integer_plateau_sum_site_approximation
    (p : PMF T) (H : ℝ) (K : ℕ) (rows : Finset (Finset α))
    (D : A → ℕ) [∀ a, NeZero (D a)]
    (a : A → rows → ℤ) (ω : A → rows → ℝ) (shift : T → rows → ℤ)
    (coefficient : A → ℂ) {C : ℝ} (hcap : (∑ m, ‖coefficient m‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ m t, |ω m t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : A → ℕ, (∀ m, (n m : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α A n) : ℝ) ≤
        Fintype.card A * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (c : PlateauSiteIndex α A n → ℂ)
        (f : (k : PlateauSiteIndex α A n) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖c k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ y : Finset α → ℤ, (∀ s, |(y s : ℝ) / K| ≤ R) →
          ‖finiteResidueModeModel D a coefficient
              (fun m => plateauModeMixture p H (D m) K (a m) (ω m) shift)
              (fun m => integerGridResidue (D m) (fun t => booleanCoefficient y t))
              (fun t => ((booleanCoefficient y t : ℤ) : ℝ) / K) -
            ∑ k, c k * ∏ s, f k s (y s : ZMod (D k.1)) ((y s : ℝ) / K)‖ ≤ C * ε := by
  have hex (m : A) := exists_scalar_integer_plateau_site_approximation
    p H (D m) K rows (a m) (ω m) shift W (hW m) hR hε hP hRP hεP hLP
  choose n hn c f hc hf hLf he using hex
  refine ⟨n, hn, ?_, (fun k => coefficient k.1 * c k.1 k.2), (fun k => f k.1 k.2),
    ?_, ?_, ?_, ?_⟩
  · exact plateauSiteIndex_card_le (α := α) n hn
  · exact sigma_sum_coefficient_norm_le coefficient c (Real.exp_nonneg _) hcap hc
  · intro k s r x
    exact hf k.1 k.2 s r x
  · intro k s r
    exact hLf k.1 k.2 s r
  · intro y hy
    exact sigma_sum_approximation_error coefficient _ c
      (fun m k => ∏ s, f m k s (y s : ZMod (D m)) ((y s : ℝ) / K))
      hε.le hcap (fun m => he m y hy)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)

noncomputable def weightedCubePlateauCoefficient (K M : ℕ) (rows : Finset (Finset α))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card * ∏ b, weightedCubeGridCoefficient (s b) M rows k

omit [NeZero M] in
theorem weightedCubePlateauCoefficient_sum_le (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) M rows k‖) ≤ C) :
    (∑ k : F, ‖weightedCubePlateauCoefficient s K M rows k‖) ≤ C := by
  rw [← Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun k => ‖weightedCubePlateauCoefficient s K M rows k‖)]
  simp only [weightedCubePlateauCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, ← Finset.mul_sum]
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  apply (mul_le_mul_of_nonneg_left
    ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans hcap) (by positivity)).trans
  exact mul_le_of_le_one_left hC hscale

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem weightedCubePlateauMixture_model
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (z : rows → ℤ) :
    (∫ v, weightedCubePlateauApproximation s K H rows (shift v) z F ∂p.toMeasure) =
      finiteResidueModeModel (fun k : F => D k) (fun k => a k)
        (fun k => weightedCubePlateauCoefficient s K M rows k)
        (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift)
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / K) := by
  rw [weightedCubePlateauMixture_expansion s p hK H rows shift z F D a ω hfreq]
  let term (k : rows → Fin M) := weightedCubePlateauCoefficient s K M rows k *
    (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
      plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K))
  calc
    _ = ∑ k ∈ F, term k := by
      simp only [term, weightedCubePlateauCoefficient, Finset.mul_sum, mul_assoc]
    _ = ∑ k : F, term k := Finset.sum_subtype F (fun _ => Iff.rfl) term
    _ = _ := rfl

theorem exists_weightedCube_plateau_site_approximation
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedCubeGridCoefficient (s b) M rows k‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ N : F → ℕ, (∀ k, (N k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F N) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (β : PlateauSiteIndex α F N → ℂ)
        (f : (k : PlateauSiteIndex α F N) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖β k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ y : Finset α → ℤ, (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(∫ v, weightedCubePlateauApproximation s K H rows (shift v)
                (fun t => booleanCoefficient y t) F ∂p.toMeasure) -
            ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have htol : 0 < δ / (C + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN, hcard, β, f, hβ, hf, hLf, he⟩ :=
    exists_integer_plateau_sum_site_approximation p H K rows (fun k : F => D k)
      (fun k => a k) (fun k => ω k) shift
      (fun k => weightedCubePlateauCoefficient s K M rows k)
      (weightedCubePlateauCoefficient_sum_le s rows F hscale hcap)
      W (fun k => hW k k.property) hR htol hP hRP hδP hLP
  refine ⟨N, hN, ?_, β, f, hβ, hf, hLf, ?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro y hy
    rw [weightedCubePlateauMixture_model s p hK H rows F D a ω hfreq shift]
    apply (he y hy).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    nlinarith only [hC, hδ]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {b K M : ℕ} [NeZero M]

theorem exists_weighted_plateau_site_approximation
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin b → NormalizedScalarCubeSource α)
    (offset : B → ℤ) (p : PMF T) (hK : 0 < K) (H : ℝ)
    (rows : Finset (Finset α)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ u, weightedModerateGridCoefficient (c u) (s u) (offset u : ℝ) M rows k‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : F → ℕ, (∀ k, (n k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F n) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (β : PlateauSiteIndex α F n → ℂ)
        (f : (k : PlateauSiteIndex α F n) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖β k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ y : Finset α → ℤ, (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(∫ v, weightedModeratePlateauApproximation c s offset K H rows (shift v)
                (fun t => booleanCoefficient y t) F ∂p.toMeasure) -
            ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have htol : 0 < δ / (C + 1) := div_pos hδ (by positivity)
  obtain ⟨n, hn, hcard, β, f, hβ, hf, hLf, he⟩ :=
    exists_integer_plateau_sum_site_approximation p H K rows (fun k : F => D k)
      (fun k => a k) (fun k => ω k) shift
      (fun k => weightedPlateauModeCoefficient c s offset K M rows k)
      (weightedPlateauModeCoefficient_sum_le c s offset rows F hscale hcap)
      W (fun k => hW k k.property) hR htol hP hRP hδP hLP
  refine ⟨n, hn, ?_, β, f, hβ, hf, hLf, ?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro y hy
    rw [weightedPlateauModeModel_grid_value c s offset p hK H rows F D a ω hfreq shift]
    apply (he y hy).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    nlinarith

end Erdos3

end

end OAI
