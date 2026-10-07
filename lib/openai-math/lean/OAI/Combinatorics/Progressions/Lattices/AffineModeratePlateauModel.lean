/- Modified for ProveIt: use Mathlib v4.32.0's generic prod_le_prod'
for product comparisons. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
import OAI.Combinatorics.Progressions.Probability.AllocatedActiveAxisSourceLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

noncomputable def finiteResidueModeModel (residue : ∀ a, J → ZMod (D a)) (x : J → ℝ) : ℂ :=
  ∑ a, coefficient a * (star (rationalGridPhase (D a) (frequency a) (residue a)) * mode a x)

theorem finiteResidueModeModel_norm {C : ℝ}
    (hcap : (∑ a, ‖coefficient a‖) ≤ C) (hmode : ∀ a x, ‖mode a x‖ ≤ 1)
    (residue : ∀ a, J → ZMod (D a)) (x : J → ℝ) :
    ‖finiteResidueModeModel D frequency coefficient mode residue x‖ ≤ C := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun a _ => ?_)).trans hcap
  rw [norm_mul, norm_mul, norm_star, rationalGridPhase_norm, one_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hmode a x)

theorem finiteResidueModeModel_lipschitz (C L : ℝ≥0)
    (hcap : (∑ a, ‖coefficient a‖) ≤ C) (hmode : ∀ a, LipschitzWith L (mode a))
    (residue : ∀ a, J → ZMod (D a)) :
    LipschitzWith (C * L) (finiteResidueModeModel D frequency coefficient mode residue) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold finiteResidueModeModel
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, ‖coefficient a * (star (rationalGridPhase (D a) (frequency a) (residue a)) * mode a x) -
        coefficient a * (star (rationalGridPhase (D a) (frequency a) (residue a)) * mode a y)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a, ‖coefficient a‖ * ((L : ℝ) * dist x y) := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, ← mul_sub, norm_mul, norm_mul, norm_star, rationalGridPhase_norm, one_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using (hmode a).dist_le_mul x y) (norm_nonneg _)
    _ = (∑ a, ‖coefficient a‖) * ((L : ℝ) * dist x y) := (Finset.sum_mul _ _ _).symm
    _ ≤ (C : ℝ) * ((L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_right hcap (mul_nonneg L.coe_nonneg dist_nonneg)
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

theorem finiteResidueModeModel_residue_card [DecidableEq A] [DecidableEq J]
    (Q : ℕ) (hQ : ∀ a, D a ≤ Q) :
    Fintype.card (∀ a, J → ZMod (D a)) ≤ Q ^ (Fintype.card A * Fintype.card J) := by
  classical
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, ZMod.card]
  calc
    ∏ a, D a ^ Fintype.card J ≤ ∏ _a : A, Q ^ Fintype.card J :=
      Finset.prod_le_prod' (fun a _ => Nat.pow_le_pow_left (hQ a) _)
    _ = Q ^ (Fintype.card A * Fintype.card J) := by
      simp only [Finset.prod_const, Finset.card_univ, ← pow_mul, Nat.mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

noncomputable def weightedAffineModerateIntegerBlock {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : ℤ)
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) : J → ℤ :=
  fun S => (offset + (x.1 none : ℤ)) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u j) (v j) (fun r => (x.2 j r : ℤ))) S

theorem weightedAffineModerateGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerSource c s) (weightedAffineModerateIntegerBlock c s u v J offset) M k =
      weightedAffineModerateGridCoefficient c s (fun j i => (u j i : ℝ)) v (offset : ℝ) M J k := by
  unfold integerGridCoefficient weightedModerateIntegerSource
  rw [FiniteProbabilityWeights.complexMean_prod]
  change c.source.complexMean _ = c.source.complexMean _
  congr 1
  funext z
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  simp only [weightedAffineModerateIntegerBlock, integerBooleanBlockJet_scaled_pairing]
  simp only [affineIntegerCubeCoordinates, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rfl

noncomputable def weightedAffineModerateIntegerJetSum {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length)) : J → ℤ :=
  shift + ∑ b, weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) J (offset b) (x b)

theorem weightedAffineModerateIntegerJetSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerProductSource c s)
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) M k =
        rectangularGridCharacter M k shift * ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k := by
  have h := independent_integerGridCoefficient (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b => weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) J (offset b)) shift M k
  unfold weightedModerateIntegerProductSource weightedAffineModerateIntegerJetSum
  simpa only [weightedAffineModerateGridCoefficient_eq_image] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCoordinate_mem {L H step : ℕ} (c z : ℤ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hz : z ∈ Finset.Ico (0 : ℤ) (H : ℤ)) :
    c + (step : ℤ) * z ∈ Finset.Ico (0 : ℤ) (L : ℤ) := by
  apply hsubset
  rw [integerProgressionSupport, mem_translateSupport]
  exact Finset.mem_image.mpr ⟨z, hz, by change (step : ℤ) * z = _; ring⟩

theorem NormalizedScalarCubeSource.source_cube {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (x : IntegerScalarCubeBox I s.length)
    (hx : s.source.weight x ≠ 0) : IntegerScalarCube s.length (fun i => (x i : ℤ)) := by
  have hb : s.baseLaw.weight x ≠ 0 := (mul_ne_zero_iff.mp hx).1
  have hp := lt_of_le_of_ne (s.baseLaw.nonneg x) hb.symm
  rw [NormalizedScalarCubeSource.baseLaw, scalarCubeResidueWeights,
    FiniteProbabilityWeights.condition_weight_pos_iff] at hp
  have h1 := hp.2
  rw [integerScalarCubeWeights, FiniteProbabilityWeights.condition_weight_pos_iff] at h1
  exact (mem_integerScalarCubeSet s.length x).mp h1.1

theorem containedProgressionCoordinate_bound {I : Type*} [Fintype I] [DecidableEq I]
    {L H step : ℕ} (c : ℤ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (x : IntegerScalarCubeBox I H) (hx : IntegerScalarCube H (fun i => (x i : ℤ))) (i : Option I) :
    |(if i = none then c else 0) + (step : ℤ) * (x i : ℤ)| ≤ L := by
  have hb := integerScalarCube_coordinates (integerScalarCube_progression c hsubset _ hx) i
  exact abs_le.mpr ⟨hb.1.le, hb.2.le⟩

theorem weightedAffineModerateIntegerJetSum_box_bound
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (T : ℕ) (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : ∀ b, ((c b).length : ℝ) * (T : ℝ) ^ n ≤ A * K)
    (shift : rows → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length))
    (hcoord : ∀ b j i,
      |affineIntegerCubeCoordinates (u b j) (v b j) (fun i => ((x b).2 j i : ℤ)) i| ≤ T)
    (t : rows) :
    |(weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) n (Fintype.card B) A * K := by
  have hb (b : B) : |weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) rows 0 (x b) t| ≤
      ((c b).length : ℤ) * ((2 : ℤ) ^ t.val.card *
        ∏ _j : Fin n, ((Fintype.card I + 1 : ℕ) : ℤ) * T) := by
    unfold weightedAffineModerateIntegerBlock
    rw [zero_add, abs_mul]
    exact mul_le_mul (integerScalarCubeBox_coordinate_abs (x b).1 none)
      (integerBooleanBlockJet_bound _ (fun _ => T) (fun j i => hcoord b j i) t)
      (abs_nonneg _) (Nat.cast_nonneg _)
  have hs : |weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t - shift t| ≤
      ∑ b, ((c b).length : ℤ) * ((2 : ℤ) ^ t.val.card *
        ∏ _j : Fin n, ((Fintype.card I + 1 : ℕ) : ℤ) * T) := by
    simp only [weightedAffineModerateIntegerJetSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ => hb b))
  have hs' : |(weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
      ∑ b, ((c b).length : ℝ) * ((2 : ℝ) ^ t.val.card *
        (((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (T : ℝ) ^ n)) := by
    have hh : |(weightedAffineModerateIntegerJetSum c s u v rows (fun _ => 0) shift x t : ℝ) - shift t| ≤
        ∑ b, ((c b).length : ℝ) * ((2 : ℝ) ^ t.val.card *
          ∏ _j : Fin n, ((Fintype.card I + 1 : ℕ) : ℝ) * T) := by
      exact_mod_cast hs
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
  apply hs'.trans
  calc
    _ = ∑ b, (2 : ℝ) ^ t.val.card * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n *
        (((c b).length : ℝ) * (T : ℝ) ^ n) := by
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ _b : B, (2 : ℝ) ^ n * ((Fintype.card I + 1 : ℕ) : ℝ) ^ n * (A * K) := by
      apply Finset.sum_le_sum
      intro b _
      apply (mul_le_mul_of_nonneg_left (hvol b) (by positivity)).trans
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hrows t t.property)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (by positivity)) (mul_nonneg hA hK)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockJetScaleBound]
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

theorem weightedAffineModerateProductSource_jet_sum_law
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) :
    ((weightedModerateIntegerProductSource c s).toPMF).map
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j q => (y j q : ℤ)))).map
              (fun y => shift + ∑ b, fun r : J => (offset b + a b) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u b j) (v b j) (y b j)) r)) := by
  have hp := congrArg (fun p : PMF (B → ℤ × (Fin n → Option I → ℤ)) =>
    p.map (fun z => shift + ∑ b, fun r : J =>
      (offset b + (z b).1) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u b j) (v b j) ((z b).2 j)) r))
    (weightedModerateProductSource_pair_law c s)
  rw [PMF.map_comp, PMF.map_bind] at hp
  change ((weightedModerateIntegerProductSource c s).toPMF).map
    (fun x => shift + ∑ b, fun r : J => (offset b + ((x b).1 none : ℤ)) *
      integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u b j) (v b j) (fun q => ((x b).2 j q : ℤ))) r) = _
  simpa only [PMF.map_comp, Function.comp_def] using hp

theorem weightedAffineModerateProductSource_affine_law
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) :
    (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j => affineIntegerCubeCoordinates (u b j) (v b j) (fun i => (y j i : ℤ))))).map
              (fun y => shift + ∑ b, fun r : J => (offset b + a b) * integerBooleanBlockJet (y b) r)) := by
  have hm := dependentProductPMF_map
    (fun b => (dependentProductPMF (fun j => (s b j).source.toPMF)).map
      (fun y j i => (y j i : ℤ)))
    (fun b y j => affineIntegerCubeCoordinates (u b j) (v b j) (y j))
  simp only [PMF.map_comp, Function.comp_def] at hm
  have ht := congrArg (fun p : PMF (B → Fin n → Option I → ℤ) =>
    (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
      (fun a => p.map (fun y => shift + ∑ b, fun r : J =>
        (offset b + a b) * integerBooleanBlockJet (y b) r))) hm
  refine (weightedAffineModerateProductSource_jet_sum_law c s u v J offset shift).trans ?_
  simpa only [PMF.map_comp, Function.comp_def] using ht

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affineWeightedCubeIntegerSum_box_bound
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (T : ℕ) (rows : Finset (Finset I)) (hrows : ∀ t ∈ rows, t.card ≤ n + 1)
    {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hvol : (T : ℝ) ^ (n + 1) ≤ A * K)
    (shift : rows → ℤ) (x : ∀ b j, IntegerScalarCubeBox I (s b j).length)
    (hcoord : ∀ b j i,
      |affineIntegerCubeCoordinates (u b j) (v b j) (fun i => (x b j i : ℤ)) i| ≤ T)
    (t : rows) :
    |(affineWeightedCubeIntegerSum s u v rows shift x t : ℝ) - shift t| ≤
      blockJetScaleBound (Fintype.card I) (n + 1) (Fintype.card B) A * K := by
  have hs : |affineWeightedCubeIntegerSum s u v rows shift x t - shift t| ≤
      ∑ _b : B, (2 : ℤ) ^ t.val.card *
        ∏ _j : Fin (n + 1), ((Fintype.card I + 1 : ℕ) : ℤ) * T := by
    simp only [affineWeightedCubeIntegerSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun b _ =>
      integerBooleanBlockJet_bound _ (fun _ => T) (fun j i => hcoord b j i) t)
  have hs' : |(affineWeightedCubeIntegerSum s u v rows shift x t : ℝ) - shift t| ≤
      ∑ _b : B, (2 : ℝ) ^ t.val.card *
        (((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (T : ℝ) ^ (n + 1)) := by
    have hh : |(affineWeightedCubeIntegerSum s u v rows shift x t : ℝ) - shift t| ≤
        ∑ _b : B, (2 : ℝ) ^ t.val.card *
          ∏ _j : Fin (n + 1), ((Fintype.card I + 1 : ℕ) : ℝ) * T := by exact_mod_cast hs
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh
  apply hs'.trans
  calc
    _ ≤ ∑ _b : B, (2 : ℝ) ^ (n + 1) * ((Fintype.card I + 1 : ℕ) : ℝ) ^ (n + 1) * (A * K) := by
      apply Finset.sum_le_sum
      intro b _
      rw [← mul_assoc]
      apply (mul_le_mul_of_nonneg_left hvol (by positivity)).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hrows t t.property)) (by positivity))
        (mul_nonneg hA hK)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, blockJetScaleBound]
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def weightedAffineModerateGridApproximation {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ)
    (S : Finset (J → Fin M)) : ℂ :=
  ((K : ℂ) / M) ^ J.card * ∑ k ∈ S,
    (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k) *
      (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z))

theorem weightedAffineModerateGridDensity_fourier {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ) :
    (integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) K M z : ℂ) =
        weightedAffineModerateGridApproximation c s u v K M J offset shift z Finset.univ := by
  rw [integerGridDensity_fourier]
  simp only [weightedAffineModerateGridApproximation, Fintype.card_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedAffineModerateIntegerJetSum_coefficient]
  ring

theorem weightedAffineModerateGridDensity_error_of_tail {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (S : Finset (J → Fin M))
    {ε : ℝ} (htail : spectrumTail S (fun k =>
      ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k‖) ≤ ε)
    (shift z : J → ℤ) :
    ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
        (weightedAffineModerateIntegerJetSum c s u v J offset shift) K M z : ℂ) -
      weightedAffineModerateGridApproximation c s u v K M J offset shift z S‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  let ψ k := rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_mul, norm_star, rectangularGridCharacter_norm, one_mul, le_refl]
  have hb := (finite_series_truncation_le S
    (fun k => ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k) ψ hψ).trans htail
  rw [weightedAffineModerateGridDensity_fourier]
  unfold weightedAffineModerateGridApproximation
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

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
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

noncomputable def weightedAffineModeratePlateauApproximation (K : ℕ) (H : ℝ)
    (rows : Finset (Finset I)) (shift z : rows → ℤ) (F : Finset (rows → Fin M)) : ℂ :=
  (normalizedSupportPlateau H (fun t => ((z t : ℝ) - shift t) / K) : ℂ) *
    weightedAffineModerateGridApproximation c s u v K M rows offset shift z F

theorem weightedAffineModeratePlateauApproximation_split_periods
    (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    weightedAffineModeratePlateauApproximation c s u v offset K H rows shift z F =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k) *
          (rationalGridPhase (D k) (a k) (integerGridResidue (D k) (shift - z)) *
            plateauFourierMode H (fun t => -ω k t) (fun t => ((z t : ℝ) - shift t) / K)) := by
  unfold weightedAffineModeratePlateauApproximation weightedAffineModerateGridApproximation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← plateau_grid_character_split H hK k (a k) (ω k) (hfreq k hk) shift z]
  ring

theorem weightedAffineModeratePlateauMixture_expansion
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I))
    (shift : T → rows → ℤ) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    (∫ zeta, weightedAffineModeratePlateauApproximation c s u v offset K H rows (shift zeta) z F ∂p.toMeasure) =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k) *
          (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
            plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K)) := by
  simp_rw [weightedAffineModeratePlateauApproximation_split_periods c s u v offset hK H rows _ z F D a ω hfreq]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, plateauModeMixture_grid_factor]
  · intro k _
    apply Integrable.const_mul
    apply pmf_integrable_of_norm_le p _ (B := 1)
    intro zeta
    rw [norm_mul, rationalGridPhase_norm, one_mul]
    exact plateauFourierMode_norm _ _ _

noncomputable def weightedAffinePlateauModeCoefficient (K M : ℕ) (rows : Finset (Finset I))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card *
    ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k

omit [NeZero M] in
theorem weightedAffinePlateauModeCoefficient_sum_le (rows : Finset (Finset I))
    (F : Finset (rows → Fin M)) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k‖) ≤ C) :
    (∑ k : F, ‖weightedAffinePlateauModeCoefficient c s u v offset K M rows k‖) ≤ C := by
  rw [← Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun k => ‖weightedAffinePlateauModeCoefficient c s u v offset K M rows k‖)]
  simp only [weightedAffinePlateauModeCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, ← Finset.mul_sum]
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  apply (mul_le_mul_of_nonneg_left
    ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans hcap) (by positivity)).trans
  exact mul_le_of_le_one_left hC hscale

noncomputable def weightedAffinePlateauModeModel (p : PMF T) (H : ℝ) (K : ℕ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (shift : T → rows → ℤ) (residue : ∀ k : F, rows → ZMod (D k)) (x : rows → ℝ) : ℂ :=
  finiteResidueModeModel (fun k : F => D k) (fun k => a k)
    (fun k => weightedAffinePlateauModeCoefficient c s u v offset K M rows k)
    (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift) residue x

theorem weightedAffinePlateauModeModel_grid_value (p : PMF T) (hK : 0 < K) (H : ℝ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (z : rows → ℤ) :
    (∫ zeta, weightedAffineModeratePlateauApproximation c s u v offset K H rows (shift zeta) z F ∂p.toMeasure) =
      weightedAffinePlateauModeModel c s u v offset p H K rows F D a ω shift
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / K) := by
  rw [weightedAffineModeratePlateauMixture_expansion c s u v offset p hK H rows shift z F D a ω hfreq]
  let term (k : rows → Fin M) := weightedAffinePlateauModeCoefficient c s u v offset K M rows k *
    (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
      plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K))
  calc
    _ = ∑ k ∈ F, term k := by
      simp only [term, weightedAffinePlateauModeCoefficient, Finset.mul_sum, mul_assoc]
    _ = ∑ k : F, term k := Finset.sum_subtype F (fun _ => Iff.rfl) term
    _ = _ := rfl

end Erdos3

end

end OAI
