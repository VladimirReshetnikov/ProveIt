import GowersSzemeredi.Proofs18SinglePieceCoverInverseFejer
import GowersSzemeredi.Proofs16SinglePieceCoverGlobalSide

/-! **The joint-cover inverse step under the Fejér θ₁ and the tight radius**
(Notes L.16d).

The Fejér instance of `Proofs18SinglePieceCoverInverse`, generated from it
by a script with a guard that no printed parameter survives:
* the frequency box comes from the explicit Fejér Lemma 15.6
  (`fejer_product_of_density_lower_explicit`), so the arrangement density is
  `fejerThetaOne α (α/2) k` and the modulus threshold is
  `fejerProductThreshold k (α/2) (α/2)`;
* the lift is `single_piece_lift_global_cover_with` at that density and the
  tight radius `tightZeta (θ₁′/4)`;
* the definitions `singlePieceGlobalF`, `singlePieceGlobalDensityF`,
  `singlePieceGlobalQmaxF`, `singlePieceGlobalWidthF`,
  `SinglePieceGlobalScaleF`, `singlePieceEtaF` and
  `SinglePieceModulusConditionsF` are the corpus's `…C` with `globalBudgetW`,
  `coverRho1W`, `coverRemWidthW` at the Fejér density.

`single_piece_inverse_step_global_cover_fejer` is the inverse step the
Section 18 envelope consumes.

Moved here from `Proofs18SinglePieceCoverInverseFejer`, which keeps only what
the final route uses. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open Classical

/-- The final density. -/
def singlePieceGlobalDensityF (Qb : Nat → Real → Real → Real → Real)
    (theta gamma : Real) (k : Nat) : Real :=
  singlePieceDensity (singlePieceGlobalF Qb theta gamma k)
    (spectrumPieceRho (fun t => t / 2) (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k)) 1

/-- The final width. -/
def singlePieceGlobalWidthF (Qb Eb : Nat → Real → Real → Real → Real)
    (theta gamma : Real) (k : Nat) (eps : Nat → Real) (m q : Nat) : Nat :=
  Nat.sqrt (coverWidth (Eb k gamma (globalBudgetW (fejerThetaOne theta gamma k) k))
    (singlePieceGlobalF Qb theta gamma k
      (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k)) 1))
    (coverWidth (Eb k gamma (globalBudgetW (fejerThetaOne theta gamma k) k))
      (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k)) 1)
      ⌈spectrumCellWidth (tightZeta (fejerThetaOne theta gamma k / 4)) m (eps q) / 8⌉₊) - 1) - 1

/-- The scale conditions at one modulus. -/
def SinglePieceGlobalScaleF (Qb Eb : Nat → Real → Real → Real → Real) (theta gamma : Real) (k : Nat) (eps : Nat → Real)
    (thr : Nat → Nat) (N m : Nat) : Prop :=
  4 ≤ coverRemWidthW Eb (fejerThetaOne theta gamma k) gamma k N ∧
  1 ≤ m ∧
  m ≤ coverWidth (Eb k (section16Delta (fejerThetaOne theta gamma k))
      (globalBudgetW (fejerThetaOne theta gamma k) k))
    (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k / 2)
    ⌈(coverRemWidthW Eb (fejerThetaOne theta gamma k) gamma k N : Real) / 8⌉₊ ∧
  ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxF Qb theta gamma k →
    thr q ≤ m ∧ 4 ≤ spectrumCellWidth (tightZeta (fejerThetaOne theta gamma k / 4)) m (eps q) ∧
    2 ≤ spectrumPieceRho (fun t => t / 2) (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k) ^ 3 *
      spectrumCellWidth (tightZeta (fejerThetaOne theta gamma k / 4)) m (eps q) ∧
    2 ≤ coverWidth (Eb k gamma (globalBudgetW (fejerThetaOne theta gamma k) k))
        (singlePieceGlobalF Qb theta gamma k
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k)) 1))
      (coverWidth (Eb k gamma (globalBudgetW (fejerThetaOne theta gamma k) k))
        (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
          (coverRho1W Qb (fejerThetaOne theta gamma k) gamma k)) 1)
        ⌈spectrumCellWidth (tightZeta (fejerThetaOne theta gamma k / 4)) m (eps q) / 8⌉₊)

/-- **The single-piece lift from global-to-local covers**, packaged. -/
theorem single_piece_lift_global_cover_fejer {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    (hEb1 : ∀ l g t s, 0 < s → s ≤ 1 → Eb l g t s ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hB : fejerThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) (m : Nat)
    (hscale : SinglePieceGlobalScaleF Qb Eb theta gamma k eps thr N m) :
    ∃ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxF Qb theta gamma k ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        singlePieceGlobalWidthF Qb Eb theta gamma k eps m q ≤ S.width ∧
        singlePieceGlobalDensityF Qb theta gamma k * S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  obtain ⟨hL4, hm1, hm, hpar⟩ := hscale
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  obtain ⟨hz0, hz2⟩ := tightZeta_pos_le_half ha0 (by linarith)
  exact single_piece_lift_global_cover_with hk ha0 haS (tightZeta_condition ha0) hz0 hz2 hg hg1
    hcov hQb hEb hEb1 eps thr hretile B phi hB hprodB hL4 m hm1 hm hpar

/-- **A dense multilinear frequency box from global-to-local covers.** -/
theorem single_piece_frequency_box_global_cover_fejer {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    (hEb1 : ∀ l g t s, 0 < s → s ≤ 1 → Eb l g t s ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : fejerProductThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real)) (m : Nat)
    (hscale : SinglePieceGlobalScaleF Qb Eb alpha (alpha / 2) k eps thr N m)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxF Qb alpha (alpha / 2) k ∧
      ∃ (P : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        P.IsProper ∧ IsMultilinear mu ∧
        singlePieceGlobalWidthF Qb Eb alpha (alpha / 2) k eps m q ≤ P.width ∧
        singlePieceGlobalDensityF Qb alpha (alpha / 2) k * P.carrier.card ≤
          section16LargeMultilinearFrequencyCount f P mu alpha := by
  have ha1 : alpha ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := by positivity
  have hg1 : alpha / 2 ≤ 1 := by linarith
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ :=
    section16_large_frequency_graph (k := k + 1) alpha ha ha1 f hf hnot
  obtain ⟨B', hB'B, harr1, harr2⟩ := fejer_product_of_density_lower_explicit k (alpha / 2)
    (alpha / 2) hk hg hg1 hg hg1 N hN (Fact.out : N.Prime) hodd B phi hBmass hprod
  have hθ1 := fejerThetaOne_half_eq alpha (alpha / 2) k
  have hB : fejerThetaOne alpha (alpha / 2) k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B' ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B' ≤
        respectedGeneralArrangementCount 8 B' phi := by
    refine ⟨?_, ?_⟩
    · rw [hθ1]; exact harr1
    · rw [← two_inv_pow_44_eq_rpow]; exact harr2
  obtain ⟨q, hq, S, mu, hS, hmu, hSw, hcount⟩ := single_piece_lift_global_cover_fejer hk ha ha1 hg hg1
    hcov hQb hEb hEb1 eps thr hretile B' phi hB (hprod.mono hB'B) m hscale
  refine ⟨q, hq, S, mu, hS, hmu, hSw, hcount.trans ?_⟩
  unfold section16LargeMultilinearFrequencyCount countWhere
  exact_mod_cast Finset.card_le_card fun z hz => by
    obtain ⟨hzB', hzS, hzmu⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzS, ?_⟩
    rw [← hzmu]
    exact hfreq z (hB'B hzB')

/-- The localization parameter of the single-piece route. -/
def singlePieceEtaF (Qb : Nat → Real → Real → Real → Real) (alpha : Real)
    (k : Nat) : Real :=
  (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) *
    (singlePieceGlobalDensityF Qb alpha (alpha / 2) k / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)

theorem singlePieceGlobalDensityF_pos {Qb : Nat → Real → Real → Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s) :
    0 < singlePieceGlobalDensityF Qb alpha (alpha / 2) k := by
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_bounds k ha ha1 (show (0 : Real) < alpha / 2 by positivity)
    (show alpha / 2 ≤ 1 by linarith)
  obtain ⟨_, _⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  obtain ⟨hr1, hr1le⟩ := coverRho1W_pos_le Qb hQb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k hfa0 hfaS
  have hr2 : 0 < spectrumPieceRho (fun t => t / 2) (coverRho1W Qb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k) ∧
      spectrumPieceRho (fun t => t / 2) (coverRho1W Qb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k) ≤ 1 := by
    unfold spectrumPieceRho
    refine ⟨by positivity, ?_⟩
    nlinarith
  have ht := singlePieceTheta_pos hr2.1 one_pos
  have ht1 := singlePieceTheta_le_one hr2.1 hr2.2 one_pos
  have hc : ∀ s, 0 < s → s ≤ 1 → 0 < singlePieceGlobalF Qb alpha (alpha / 2) k s ∧
      singlePieceGlobalF Qb alpha (alpha / 2) k s ≤ 1 := by
    intro s hs hs1
    have hq := hQb k (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k) (s / 2) (by positivity)
      (by linarith)
    unfold singlePieceGlobalF
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hc1, hc1le⟩ := hc _ ht ht1
  obtain ⟨hc2, -⟩ := hc _ hc1 hc1le
  unfold singlePieceGlobalDensityF singlePieceDensity
  exact mul_pos ht hc2

theorem singlePieceEtaF_pos {Qb : Nat → Real → Real → Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s) : 0 < singlePieceEtaF Qb alpha k := by
  have := singlePieceGlobalDensityF_pos (k := k) ha ha1 hQb
  unfold singlePieceEtaF; positivity

/-- **Localization from global-to-local covers.** -/
theorem single_piece_localization_global_cover_fejer {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    (hEb1 : ∀ l g t s, 0 < s → s ≤ 1 → Eb l g t s ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {e : Real} (he : e ≤ 1 / 2)
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : fejerProductThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real)) (m : Nat)
    (hscale : SinglePieceGlobalScaleF Qb Eb alpha (alpha / 2) k eps thr N m)
    (hwide : ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxF Qb alpha (alpha / 2) k →
      (N : Real) ^ e ≤ singlePieceGlobalWidthF Qb Eb alpha (alpha / 2) k eps m q)
    (hlarge : 4 ≤ (N : Real) ^ e)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
      PolynomialOn (k + 2) Finset.univ phi ∧
      IsPartition (fun i => (Q i).carrier) Finset.univ ∧
      (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
      (N : Real) ^ e / (6 * (k + 1 : Nat)) ≤ l ∧
      (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
      ¬ UniformOnPartition (phaseTwist f phi) (k + 1) (singlePieceEtaF Qb alpha k) Q (l + 1) := by
  obtain ⟨q, hq, P, mu, hP, hmu, hPw, hmass⟩ := single_piece_frequency_box_global_cover_fejer hk ha haHalf
    hcov hQb hEb hEb1 eps thr hretile hodd hN m hscale f hf hnot
  have h := polynomial_localization_of_dense_frequency_box (Nat.succ_pos k) P hP f mu ha
    (singlePieceGlobalDensityF_pos ha (by linarith) hQb) he hf hmu
    ((hwide q hq).trans (by exact_mod_cast hPw)) hlarge hmass
  exact h

/-- The per-modulus conditions of the single-piece inverse step. -/
def SinglePieceModulusConditionsF (Qb Eb : Nat → Real → Real → Real → Real) (alpha : Real) (k : Nat) (eps : Nat → Real) (thr : Nat → Nat)
    (e : Real) (N : Nat) : Prop :=
  Odd N ∧ fejerProductThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real) ∧
    4 ≤ (N : Real) ^ e ∧
    ∃ m : Nat, SinglePieceGlobalScaleF Qb Eb alpha (alpha / 2) k eps thr N m ∧
      ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxF Qb alpha (alpha / 2) k →
        (N : Real) ^ e ≤ singlePieceGlobalWidthF Qb Eb alpha (alpha / 2) k eps m q

/-- **The single-piece inverse step.** A degree-`(k+1)` discrepancy bound
gives a degree-`(k+2)` bound, through the single-piece frequency box. -/
theorem single_piece_inverse_step_global_cover_fejer {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    (hEb1 : ∀ l g t s, 0 < s → s ≤ 1 → Eb l g t s ≤ 1)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {e : Real} (he0 : 0 < e) (he : e ≤ 1 / 2) {beta sigma T Tloc : Real}
    (hbound : FunctionDiscrepancyBound (k + 1)
      ((singlePieceEtaF Qb alpha k / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))
      beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16)
    (hmod : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      SinglePieceModulusConditionsF Qb Eb alpha k eps thr e N) :
    FunctionDiscrepancyBound (k + 2) alpha (singlePieceEtaF Qb alpha k * beta / 4)
      (inverseStepExponent (k + 1) e sigma)
      (max (shortLocalizationThreshold (k + 1) e (6 * ((k + 1 : Nat) : Real)) T Tloc)
        (inverseStepThreshold (k + 1) (singlePieceEtaF Qb alpha k) beta e
          (6 * ((k + 1 : Nat) : Real)) sigma)) := by
  refine hbound.of_short_polynomial_localization (Tloc := Tloc)
    (c := 6 * ((k + 1 : Nat) : Real)) (singlePieceEtaF_pos ha (by linarith) hQb) hb hs hs16
    he0 (by positivity) ?_
  intro N _ _ hN f hf hnot
  obtain ⟨hodd, h15, hlarge, m, hsc, hwide⟩ := hmod N hN
  exact single_piece_localization_global_cover_fejer hk ha haHalf hcov hQb hEb hEb1 eps thr
    hretile he hodd h15 m hsc hwide hlarge f hf hnot

theorem singlePieceGlobalDensityF_le_one {Qb : Nat → Real → Real → Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s) :
    singlePieceGlobalDensityF Qb alpha (alpha / 2) k ≤ 1 := by
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_bounds k ha ha1 (show (0 : Real) < alpha / 2 by positivity)
    (show alpha / 2 ≤ 1 by linarith)
  obtain ⟨_, _⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  obtain ⟨hr1, hr1le⟩ := coverRho1W_pos_le Qb hQb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k hfa0 hfaS
  have hr2 : 0 < spectrumPieceRho (fun t => t / 2) (coverRho1W Qb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k) ∧
      spectrumPieceRho (fun t => t / 2) (coverRho1W Qb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k) ≤ 1 := by
    unfold spectrumPieceRho
    refine ⟨by positivity, ?_⟩
    nlinarith
  have ht := singlePieceTheta_pos hr2.1 one_pos
  have ht1 := singlePieceTheta_le_one hr2.1 hr2.2 one_pos
  have hc : ∀ s, 0 < s → s ≤ 1 → 0 < singlePieceGlobalF Qb alpha (alpha / 2) k s ∧
      singlePieceGlobalF Qb alpha (alpha / 2) k s ≤ 1 := by
    intro s hs hs1
    have hq := hQb k (alpha / 2) (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k) (s / 2) (by positivity)
      (by linarith)
    unfold singlePieceGlobalF
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by linarith)]
    linarith
  obtain ⟨hc1, hc1le⟩ := hc _ ht ht1
  obtain ⟨hc2, hc2le⟩ := hc _ hc1 hc1le
  unfold singlePieceGlobalDensityF singlePieceDensity
  calc singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (coverRho1W Qb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k)) 1 *
        singlePieceGlobalF Qb alpha (alpha / 2) k (singlePieceGlobalF Qb alpha (alpha / 2) k
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (coverRho1W Qb (fejerThetaOne alpha (alpha / 2) k) (alpha / 2) k)) 1)) ≤ 1 * 1 :=
        mul_le_mul ht1 hc2le hc2.le zero_le_one
    _ = 1 := one_mul 1

end

end LeanProofs.GowersSzemeredi
