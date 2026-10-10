import GowersSzemeredi.Proofs16SinglePieceGlobalFrequency
import GowersSzemeredi.Proofs17DenseFrequencyLocalization
import GowersSzemeredi.Proofs18ShortLocalizationInverse
import GowersSzemeredi.Proofs18FejerCubicDiscrepancy
import GowersSzemeredi.Proofs18StructuralInverseParameters

/-! The single-piece lift, step 7 (Notes L.1): an inverse step from
global-to-local covers.

* `single_piece_localization_global`: the frequency box of
  `single_piece_frequency_box_global` has width `≥ N^e`. It is therefore
  localized by `polynomial_localization_of_dense_frequency_box` at
  parameter `singlePieceEta`, which is
  `2^(−2(k+2)³)·(ρ/2^(k+1))·α²/4`.
* `single_piece_inverse_step_global`: a degree-`(k+1)` discrepancy bound
  gives a degree-`(k+2)` bound at parameter `η·β/4`, via
  `FunctionDiscrepancyBound.of_short_polynomial_localization`.
* `single_piece_quartic_inverse_global`: the step at `k = 2` on the proved
  Fejér cubic bound. Its inputs are `PolyCoverAt 1` (proved),
  `PolyCoverAt 2` (the open core), the retiled linearity bound, and the
  per-modulus scale conditions.

Here `ρ = singlePieceGlobalDensity` is polynomial in `α` whenever `Qb` is
polynomial; the cover route has `exp(−poly)` in its place (Notes K.4). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The localization parameter of the single-piece route. -/
def singlePieceEta (Qb : Nat → Real → Real → Real → Real) (C : Real → Real) (alpha : Real)
    (k : Nat) : Real :=
  (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) *
    (singlePieceGlobalDensity Qb C alpha (alpha / 2) k / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)

theorem singlePieceGlobalDensity_pos {Qb : Nat → Real → Real → Real → Real} {C : Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) :
    0 < singlePieceGlobalDensity Qb C alpha (alpha / 2) k := by
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (by positivity)
    (by linarith)
  have hg2 : 0 < globalTheta2 alpha (alpha / 2) k := by unfold globalTheta2; positivity
  have hg21 : globalTheta2 alpha (alpha / 2) k ≤ 1 := by unfold globalTheta2; linarith
  obtain ⟨hr1, hr1le⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) (2 ^ k - 1) _ hg2 hg21
  have hr2 : 0 < spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1 C alpha (alpha / 2) k) ∧
      spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1 C alpha (alpha / 2) k) ≤ 1 := by
    unfold spectrumPieceRho singlePieceGlobalRho1
    refine ⟨by positivity, ?_⟩
    nlinarith
  have ht := singlePieceTheta_pos hr2.1 one_pos
  have ht1 := singlePieceTheta_le_one hr2.1 hr2.2 one_pos
  have hc : ∀ s, 0 < s → s ≤ 1 → 0 < singlePieceGlobalC Qb alpha (alpha / 2) k s ∧
      singlePieceGlobalC Qb alpha (alpha / 2) k s ≤ 1 := by
    intro s hs hs1
    have hq := hQb k (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2) (by positivity)
      (by linarith)
    unfold singlePieceGlobalC
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hc1, hc1le⟩ := hc _ ht ht1
  obtain ⟨hc2, -⟩ := hc _ hc1 hc1le
  unfold singlePieceGlobalDensity singlePieceDensity
  exact mul_pos ht hc2

theorem singlePieceEta_pos {Qb : Nat → Real → Real → Real → Real} {C : Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) : 0 < singlePieceEta Qb C alpha k := by
  have := singlePieceGlobalDensity_pos (k := k) ha ha1 hQb hC
  unfold singlePieceEta; positivity

/-- **Localization from global-to-local covers.** -/
theorem single_piece_localization_global {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {C : Real → Real} {W : Real → Nat → Nat}
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, C t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, W t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l (alpha / 2) (globalBudget alpha (alpha / 2) k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {e : Real} (he : e ≤ 1 / 2)
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real)) (m : Nat)
    (hscale : SinglePieceGlobalScale Qb Eb C W alpha (alpha / 2) k eps thr N m)
    (hwide : ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmax Qb C alpha (alpha / 2) k →
      (N : Real) ^ e ≤ singlePieceGlobalWidth Qb Eb C alpha (alpha / 2) k eps m q)
    (hlarge : 4 ≤ (N : Real) ^ e)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
      PolynomialOn (k + 2) Finset.univ phi ∧
      IsPartition (fun i => (Q i).carrier) Finset.univ ∧
      (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
      (N : Real) ^ e / (6 * (k + 1 : Nat)) ≤ l ∧
      (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
      ¬ UniformOnPartition (phaseTwist f phi) (k + 1) (singlePieceEta Qb C alpha k) Q (l + 1) := by
  obtain ⟨q, hq, P, mu, hP, hmu, hPw, hmass⟩ := single_piece_frequency_box_global hk ha haHalf
    hcov hQb hEb hC hW hCle hWle eps thr hretile hodd hN m hscale f hf hnot
  have h := polynomial_localization_of_dense_frequency_box (Nat.succ_pos k) P hP f mu ha
    (singlePieceGlobalDensity_pos ha (by linarith) hQb hC) he hf hmu
    ((hwide q hq).trans (by exact_mod_cast hPw)) hlarge hmass
  exact h


/-- The per-modulus conditions of the single-piece inverse step. -/
def SinglePieceModulusConditions (Qb Eb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (W : Real → Nat → Nat) (alpha : Real) (k : Nat) (eps : Nat → Real) (thr : Nat → Nat)
    (e : Real) (N : Nat) : Prop :=
  Odd N ∧ lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real) ∧
    4 ≤ (N : Real) ^ e ∧
    ∃ m : Nat, SinglePieceGlobalScale Qb Eb C W alpha (alpha / 2) k eps thr N m ∧
      ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmax Qb C alpha (alpha / 2) k →
        (N : Real) ^ e ≤ singlePieceGlobalWidth Qb Eb C alpha (alpha / 2) k eps m q

/-- **The single-piece inverse step.** A degree-`(k+1)` discrepancy bound
gives a degree-`(k+2)` bound, through the single-piece frequency box. -/
theorem single_piece_inverse_step_global {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {C : Real → Real} {W : Real → Nat → Nat}
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, C t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, W t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l (alpha / 2) (globalBudget alpha (alpha / 2) k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {e : Real} (he0 : 0 < e) (he : e ≤ 1 / 2) {beta sigma T Tloc : Real}
    (hbound : FunctionDiscrepancyBound (k + 1)
      ((singlePieceEta Qb C alpha k / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))
      beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16)
    (hmod : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      SinglePieceModulusConditions Qb Eb C W alpha k eps thr e N) :
    FunctionDiscrepancyBound (k + 2) alpha (singlePieceEta Qb C alpha k * beta / 4)
      (inverseStepExponent (k + 1) e sigma)
      (max (shortLocalizationThreshold (k + 1) e (6 * ((k + 1 : Nat) : Real)) T Tloc)
        (inverseStepThreshold (k + 1) (singlePieceEta Qb C alpha k) beta e
          (6 * ((k + 1 : Nat) : Real)) sigma)) := by
  refine hbound.of_short_polynomial_localization (Tloc := Tloc)
    (c := 6 * ((k + 1 : Nat) : Real)) (singlePieceEta_pos ha (by linarith) hQb hC) hb hs hs16
    he0 (by positivity) ?_
  intro N _ _ hN f hf hnot
  obtain ⟨hodd, h15, hlarge, m, hsc, hwide⟩ := hmod N hN
  exact single_piece_localization_global hk ha haHalf hcov hQb hEb hC hW hCle hWle eps thr
    hretile he hodd h15 m hsc hwide hlarge f hf hnot


theorem singlePieceGlobalDensity_le_one {Qb : Nat → Real → Real → Real → Real}
    {C : Real → Real} {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) :
    singlePieceGlobalDensity Qb C alpha (alpha / 2) k ≤ 1 := by
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (by positivity)
    (by linarith)
  have hg2 : 0 < globalTheta2 alpha (alpha / 2) k := by unfold globalTheta2; positivity
  have hg21 : globalTheta2 alpha (alpha / 2) k ≤ 1 := by unfold globalTheta2; linarith
  obtain ⟨hr1, hr1le⟩ := nestC_pos_le (c := fun _ => C) (fun _ => hC) (2 ^ k - 1) _ hg2 hg21
  have hr2 : 0 < spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1 C alpha (alpha / 2) k) ∧
      spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1 C alpha (alpha / 2) k) ≤ 1 := by
    unfold spectrumPieceRho singlePieceGlobalRho1
    refine ⟨by positivity, ?_⟩
    nlinarith
  have ht := singlePieceTheta_pos hr2.1 one_pos
  have ht1 := singlePieceTheta_le_one hr2.1 hr2.2 one_pos
  have hc : ∀ s, 0 < s → s ≤ 1 → 0 < singlePieceGlobalC Qb alpha (alpha / 2) k s ∧
      singlePieceGlobalC Qb alpha (alpha / 2) k s ≤ 1 := by
    intro s hs hs1
    have hq := hQb k (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2) (by positivity)
      (by linarith)
    unfold singlePieceGlobalC
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hc1, hc1le⟩ := hc _ ht ht1
  obtain ⟨hc2, hc2le⟩ := hc _ hc1 hc1le
  unfold singlePieceGlobalDensity singlePieceDensity
  calc singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (singlePieceGlobalRho1 C alpha (alpha / 2) k)) 1 *
        singlePieceGlobalC Qb alpha (alpha / 2) k (singlePieceGlobalC Qb alpha (alpha / 2) k
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (singlePieceGlobalRho1 C alpha (alpha / 2) k)) 1)) ≤ 1 * 1 :=
        mul_le_mul ht1 hc2le hc2.le zero_le_one
    _ = 1 := one_mul 1

/-- The degree-three input parameter of the quartic step. -/
def singlePieceCubicInput (Qb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (alpha : Real) : Real :=
  (singlePieceEta Qb C alpha 2 / 2) / (2 * (2 + 1 + 2 : Nat) : Real) ^ (2 + 1 + 2)

/-- **A degree-four inverse theorem from global-to-local covers.** The
inputs are `PolyCoverAt 1` (proved, `polyCoverAt_one`), `PolyCoverAt 2`,
the retiled linearity bound, and the per-modulus conditions. The degree-three
base is the proved Fejér cubic bound. -/
theorem single_piece_quartic_inverse_global {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ 2 → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {C : Real → Real} {W : Real → Nat → Nat}
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (hCle : ∀ l, 1 ≤ l → l ≤ 2 → ∀ t, C t ≤ (liftLastC^[2 + 1 - l]
      (fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) 2) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ 2 → ∀ t L, W t L ≤ (liftLastW^[2 + 1 - l]
      (coverWidth (Eb l (alpha / 2) (globalBudget alpha (alpha / 2) 2)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound 2 q (eps q) (thr q))
    {e : Real} (he0 : 0 < e) (he : e ≤ 1 / 2) {Tloc : Real}
    (hmod : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      SinglePieceModulusConditions Qb Eb C W alpha 2 eps thr e N) :
    FunctionDiscrepancyBound 4 alpha
      (singlePieceEta Qb C alpha 2 *
        fejerCubicDiscrepancyParameter (singlePieceCubicInput Qb C alpha) / 4)
      (inverseStepExponent (2 + 1) e
        (min (fejerCubicDiscrepancyExponent (singlePieceCubicInput Qb C alpha)) 16))
      (max (shortLocalizationThreshold (2 + 1) e (6 * ((2 + 1 : Nat) : Real))
          (fejerCubicInverseThreshold (singlePieceCubicInput Qb C alpha)) Tloc)
        (inverseStepThreshold (2 + 1) (singlePieceEta Qb C alpha 2)
          (fejerCubicDiscrepancyParameter (singlePieceCubicInput Qb C alpha)) e
          (6 * ((2 + 1 : Nat) : Real))
          (min (fejerCubicDiscrepancyExponent (singlePieceCubicInput Qb C alpha)) 16))) := by
  have ha1 : alpha ≤ 1 := by linarith
  have heta := singlePieceEta_pos (k := 2) ha ha1 hQb hC
  have hρ1 := singlePieceGlobalDensity_le_one (k := 2) ha ha1 hQb hC
  have hin : 0 < singlePieceCubicInput Qb C alpha := by
    unfold singlePieceCubicInput; positivity
  have hin1 : singlePieceCubicInput Qb C alpha ≤ 1 := by
    have hρ0 := singlePieceGlobalDensity_pos (k := 2) ha ha1 hQb hC
    unfold singlePieceCubicInput singlePieceEta
    have h2 : (2 : Real) ^ (-(2 * ((2 + 1) + 1) ^ 3 : Int)) ≤ 1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
    have hα2 : alpha ^ 2 ≤ 1 := pow_le_one₀ ha.le ha1
    have hinner : singlePieceGlobalDensity Qb C alpha (alpha / 2) 2 / (2 : Real) ^ (2 + 1) *
        alpha ^ 2 / 4 ≤ 1 := by
      have : singlePieceGlobalDensity Qb C alpha (alpha / 2) 2 / (2 : Real) ^ (2 + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    have hη1 : (2 : Real) ^ (-(2 * ((2 + 1) + 1) ^ 3 : Int)) *
        (singlePieceGlobalDensity Qb C alpha (alpha / 2) 2 / (2 : Real) ^ (2 + 1) *
          alpha ^ 2 / 4) ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul h2 hinner (by positivity) zero_le_one
        _ = 1 := one_mul 1
    rw [div_le_one (by positivity)]
    have hpow : (1 : Real) ≤ (2 * (2 + 1 + 2 : Nat) : Real) ^ (2 + 1 + 2) := by
      exact one_le_pow₀ (by norm_num)
    linarith
  have hbase := fejer_cubic_function_discrepancy_bound hin hin1
  have hbound := hbase.mono le_rfl le_rfl (min_le_left _ 16) le_rfl
  exact single_piece_inverse_step_global (k := 2) (by norm_num) ha haHalf hcov hQb hEb hC hW
    hCle hWle eps thr hretile he0 he hbound (fejerCubicDiscrepancyParameter_pos hin)
    (lt_min (fejerCubicDiscrepancyExponent_pos hin hin1) (by norm_num)) (min_le_right _ _) hmod

end LeanProofs.GowersSzemeredi
