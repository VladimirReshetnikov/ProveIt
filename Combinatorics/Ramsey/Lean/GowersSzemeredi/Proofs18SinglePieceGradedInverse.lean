import GowersSzemeredi.Proofs16SinglePieceGradedGlobal
import GowersSzemeredi.Proofs18SinglePieceInverse
import GowersSzemeredi.Proofs05Corollary58

/-! The frequency box and the inverse step with graded vertex providers
(Notes L.10, G3b).

This is `Proofs16SinglePieceGlobalFrequency` and `Proofs18SinglePieceInverse`
with the uniform pair `(C, W)` replaced by the face-dimension families
`(Cg, Wg)`. The remainder density becomes
`singlePieceGlobalRho1G Cg θ γ k = gradedNestC Cg (vertexFaceCounts k) (k + 1) θ₂`.
Everything else is verbatim. The names carry a `G` (definitions) or
`_graded` (theorems). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The density after the remainder step. -/
def singlePieceGlobalRho1G (Cg : Nat → Real → Real) (theta gamma : Real) (k : Nat) : Real :=
  gradedNestC Cg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k)

/-- The final density. -/
def singlePieceGlobalDensityG (Qb : Nat → Real → Real → Real → Real) (Cg : Nat → Real → Real)
    (theta gamma : Real) (k : Nat) : Real :=
  singlePieceDensity (singlePieceGlobalC Qb theta gamma k)
    (spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1G Cg theta gamma k)) 1

/-- The spectrum graph-count bound. -/
def singlePieceGlobalQmaxG (Qb : Nat → Real → Real → Real → Real) (Cg : Nat → Real → Real)
    (theta gamma : Real) (k : Nat) : Real :=
  Qb k (section16Delta (section16ThetaOne theta gamma k)) (globalBudget theta gamma k)
    (singlePieceGlobalRho1G Cg theta gamma k / 2 / 2)

/-- The final width. -/
def singlePieceGlobalWidthG (Qb Eb : Nat → Real → Real → Real → Real) (Cg : Nat → Real → Real)
    (theta gamma : Real) (k : Nat) (eps : Nat → Real) (m q : Nat) : Nat :=
  Nat.sqrt (coverWidth (Eb k gamma (globalBudget theta gamma k))
    (singlePieceGlobalC Qb theta gamma k
      (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (singlePieceGlobalRho1G Cg theta gamma k)) 1))
    (coverWidth (Eb k gamma (globalBudget theta gamma k))
      (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (singlePieceGlobalRho1G Cg theta gamma k)) 1)
      ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊) - 1) - 1

/-- The scale conditions at one modulus. -/
def SinglePieceGlobalScaleG (Qb Eb : Nat → Real → Real → Real → Real) (Cg : Nat → Real → Real)
    (Wg : Nat → Real → Nat → Nat) (theta gamma : Real) (k : Nat) (eps : Nat → Real)
    (thr : Nat → Nat) (N m : Nat) : Prop :=
  4 ≤ gradedNestW Cg Wg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) N ∧
  1 ≤ m ∧
  m ≤ coverWidth (Eb k (section16Delta (section16ThetaOne theta gamma k))
      (globalBudget theta gamma k))
    (singlePieceGlobalRho1G Cg theta gamma k / 2)
    ⌈(gradedNestW Cg Wg (vertexFaceCounts k) (k + 1) (globalTheta2 theta gamma k) N : Real) / 8⌉₊ ∧
  ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxG Qb Cg theta gamma k →
    thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
    2 ≤ spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1G Cg theta gamma k) ^ 3 *
      spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
    2 ≤ coverWidth (Eb k gamma (globalBudget theta gamma k))
        (singlePieceGlobalC Qb theta gamma k
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (singlePieceGlobalRho1G Cg theta gamma k)) 1))
      (coverWidth (Eb k gamma (globalBudget theta gamma k))
        (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
          (singlePieceGlobalRho1G Cg theta gamma k)) 1)
        ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊)

/-- **The single-piece lift from global-to-local covers**, packaged. -/
theorem single_piece_lift_global_graded' {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {Cg : Nat → Real → Real} {Wg : Nat → Real → Nat → Nat}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) (hW : ∀ j t, Monotone (Wg j t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, Cg l t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l gamma (globalBudget theta gamma k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, Wg l t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l gamma (globalBudget theta gamma k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hB : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) (m : Nat)
    (hscale : SinglePieceGlobalScaleG Qb Eb Cg Wg theta gamma k eps thr N m) :
    ∃ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxG Qb Cg theta gamma k ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        singlePieceGlobalWidthG Qb Eb Cg theta gamma k eps m q ≤ S.width ∧
        singlePieceGlobalDensityG Qb Cg theta gamma k * S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  obtain ⟨hL4, hm1, hm, hpar⟩ := hscale
  exact single_piece_lift_global_graded hk ht ht1 hg hg1 hcov hQb hEb hC hW hCle hWle eps thr hretile
    B phi hB hprodB hL4 m hm1 hm hpar

/-- **A dense multilinear frequency box from global-to-local covers.** -/
theorem single_piece_frequency_box_global_graded {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {Cg : Nat → Real → Real} {Wg : Nat → Real → Nat → Nat}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) (hW : ∀ j t, Monotone (Wg j t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, Cg l t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, Wg l t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l (alpha / 2) (globalBudget alpha (alpha / 2) k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real)) (m : Nat)
    (hscale : SinglePieceGlobalScaleG Qb Eb Cg Wg alpha (alpha / 2) k eps thr N m)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxG Qb Cg alpha (alpha / 2) k ∧
      ∃ (P : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        P.IsProper ∧ IsMultilinear mu ∧
        singlePieceGlobalWidthG Qb Eb Cg alpha (alpha / 2) k eps m q ≤ P.width ∧
        singlePieceGlobalDensityG Qb Cg alpha (alpha / 2) k * P.carrier.card ≤
          section16LargeMultilinearFrequencyCount f P mu alpha := by
  have ha1 : alpha ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := by positivity
  have hg1 : alpha / 2 ≤ 1 := by linarith
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ :=
    section16_large_frequency_graph (k := k + 1) alpha ha ha1 f hf hnot
  obtain ⟨B', hB'B, harr1, harr2⟩ := lemma_15_6_of_density_lower_all_explicit k (alpha / 2)
    (alpha / 2) hg hg1 hg hg1 N hN (Fact.out : N.Prime) hodd B phi hBmass hprod
  have hθ1 : section16ThetaOne alpha (alpha / 2) k =
      (alpha / 2 * (alpha / 2) / 2) ^ (2 ^ (2 ^ (k + 5))) := by
    unfold section16ThetaOne
    congr 1
    ring
  have hB : section16ThetaOne alpha (alpha / 2) k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B' ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B' ≤
        respectedGeneralArrangementCount 8 B' phi := by
    refine ⟨?_, ?_⟩
    · rw [hθ1]; exact harr1
    · rw [← two_inv_pow_44_eq_rpow]; exact harr2
  obtain ⟨q, hq, S, mu, hS, hmu, hSw, hcount⟩ := single_piece_lift_global_graded' hk ha ha1 hg hg1
    hcov hQb hEb hC hW hCle hWle eps thr hretile B' phi hB (hprod.mono hB'B) m hscale
  refine ⟨q, hq, S, mu, hS, hmu, hSw, hcount.trans ?_⟩
  unfold section16LargeMultilinearFrequencyCount countWhere
  exact_mod_cast Finset.card_le_card fun z hz => by
    obtain ⟨hzB', hzS, hzmu⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzS, ?_⟩
    rw [← hzmu]
    exact hfreq z (hB'B hzB')

/-- The localization parameter of the single-piece route. -/
def singlePieceEtaG (Qb : Nat → Real → Real → Real → Real) (Cg : Nat → Real → Real) (alpha : Real)
    (k : Nat) : Real :=
  (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) *
    (singlePieceGlobalDensityG Qb Cg alpha (alpha / 2) k / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4)

theorem singlePieceGlobalDensityG_pos {Qb : Nat → Real → Real → Real → Real} {Cg : Nat → Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) :
    0 < singlePieceGlobalDensityG Qb Cg alpha (alpha / 2) k := by
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (by positivity)
    (by linarith)
  have hg2 : 0 < globalTheta2 alpha (alpha / 2) k := by unfold globalTheta2; positivity
  have hg21 : globalTheta2 alpha (alpha / 2) k ≤ 1 := by unfold globalTheta2; linarith
  obtain ⟨hr1, hr1le⟩ := gradedNestC_pos_le hC (vertexFaceCounts k) (k + 1) _ hg2 hg21
  have hr2 : 0 < spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1G Cg alpha (alpha / 2) k) ∧
      spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1G Cg alpha (alpha / 2) k) ≤ 1 := by
    unfold spectrumPieceRho singlePieceGlobalRho1G
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
  unfold singlePieceGlobalDensityG singlePieceDensity
  exact mul_pos ht hc2

theorem singlePieceEtaG_pos {Qb : Nat → Real → Real → Real → Real} {Cg : Nat → Real → Real}
    {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) : 0 < singlePieceEtaG Qb Cg alpha k := by
  have := singlePieceGlobalDensityG_pos (k := k) ha ha1 hQb hC
  unfold singlePieceEtaG; positivity

/-- **Localization from global-to-local covers.** -/
theorem single_piece_localization_global_graded {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {Cg : Nat → Real → Real} {Wg : Nat → Real → Nat → Nat}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) (hW : ∀ j t, Monotone (Wg j t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, Cg l t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, Wg l t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l (alpha / 2) (globalBudget alpha (alpha / 2) k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {e : Real} (he : e ≤ 1 / 2)
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real)) (m : Nat)
    (hscale : SinglePieceGlobalScaleG Qb Eb Cg Wg alpha (alpha / 2) k eps thr N m)
    (hwide : ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxG Qb Cg alpha (alpha / 2) k →
      (N : Real) ^ e ≤ singlePieceGlobalWidthG Qb Eb Cg alpha (alpha / 2) k eps m q)
    (hlarge : 4 ≤ (N : Real) ^ e)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
      PolynomialOn (k + 2) Finset.univ phi ∧
      IsPartition (fun i => (Q i).carrier) Finset.univ ∧
      (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
      (N : Real) ^ e / (6 * (k + 1 : Nat)) ≤ l ∧
      (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
      ¬ UniformOnPartition (phaseTwist f phi) (k + 1) (singlePieceEtaG Qb Cg alpha k) Q (l + 1) := by
  obtain ⟨q, hq, P, mu, hP, hmu, hPw, hmass⟩ := single_piece_frequency_box_global_graded hk ha haHalf
    hcov hQb hEb hC hW hCle hWle eps thr hretile hodd hN m hscale f hf hnot
  have h := polynomial_localization_of_dense_frequency_box (Nat.succ_pos k) P hP f mu ha
    (singlePieceGlobalDensityG_pos ha (by linarith) hQb hC) he hf hmu
    ((hwide q hq).trans (by exact_mod_cast hPw)) hlarge hmass
  exact h


/-- The per-modulus conditions of the single-piece inverse step. -/
def SinglePieceModulusConditionsG (Qb Eb : Nat → Real → Real → Real → Real) (Cg : Nat → Real → Real)
    (Wg : Nat → Real → Nat → Nat) (alpha : Real) (k : Nat) (eps : Nat → Real) (thr : Nat → Nat)
    (e : Real) (N : Nat) : Prop :=
  Odd N ∧ lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real) ∧
    4 ≤ (N : Real) ^ e ∧
    ∃ m : Nat, SinglePieceGlobalScaleG Qb Eb Cg Wg alpha (alpha / 2) k eps thr N m ∧
      ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmaxG Qb Cg alpha (alpha / 2) k →
        (N : Real) ^ e ≤ singlePieceGlobalWidthG Qb Eb Cg alpha (alpha / 2) k eps m q

/-- **The single-piece inverse step.** A degree-`(k+1)` discrepancy bound
gives a degree-`(k+2)` bound, through the single-piece frequency box. -/
theorem single_piece_inverse_step_global_graded {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {Cg : Nat → Real → Real} {Wg : Nat → Real → Nat → Nat}
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) (hW : ∀ j t, Monotone (Wg j t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, Cg l t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, Wg l t L ≤ (liftLastW^[k + 1 - l]
      (coverWidth (Eb l (alpha / 2) (globalBudget alpha (alpha / 2) k)))) t L)
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {e : Real} (he0 : 0 < e) (he : e ≤ 1 / 2) {beta sigma T Tloc : Real}
    (hbound : FunctionDiscrepancyBound (k + 1)
      ((singlePieceEtaG Qb Cg alpha k / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))
      beta sigma T)
    (hb : 0 < beta) (hs : 0 < sigma) (hs16 : sigma ≤ 16)
    (hmod : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      SinglePieceModulusConditionsG Qb Eb Cg Wg alpha k eps thr e N) :
    FunctionDiscrepancyBound (k + 2) alpha (singlePieceEtaG Qb Cg alpha k * beta / 4)
      (inverseStepExponent (k + 1) e sigma)
      (max (shortLocalizationThreshold (k + 1) e (6 * ((k + 1 : Nat) : Real)) T Tloc)
        (inverseStepThreshold (k + 1) (singlePieceEtaG Qb Cg alpha k) beta e
          (6 * ((k + 1 : Nat) : Real)) sigma)) := by
  refine hbound.of_short_polynomial_localization (Tloc := Tloc)
    (c := 6 * ((k + 1 : Nat) : Real)) (singlePieceEtaG_pos ha (by linarith) hQb hC) hb hs hs16
    he0 (by positivity) ?_
  intro N _ _ hN f hf hnot
  obtain ⟨hodd, h15, hlarge, m, hsc, hwide⟩ := hmod N hN
  exact single_piece_localization_global_graded hk ha haHalf hcov hQb hEb hC hW hCle hWle eps thr
    hretile he hodd h15 m hsc hwide hlarge f hf hnot


theorem singlePieceGlobalDensityG_le_one {Qb : Nat → Real → Real → Real → Real}
    {Cg : Nat → Real → Real} {alpha : Real} {k : Nat} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hC : ∀ j t, 0 < t → t ≤ 1 → 0 < Cg j t ∧ Cg j t ≤ 1) :
    singlePieceGlobalDensityG Qb Cg alpha (alpha / 2) k ≤ 1 := by
  obtain ⟨hθ₂, hθ₂1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (by positivity)
    (by linarith)
  have hg2 : 0 < globalTheta2 alpha (alpha / 2) k := by unfold globalTheta2; positivity
  have hg21 : globalTheta2 alpha (alpha / 2) k ≤ 1 := by unfold globalTheta2; linarith
  obtain ⟨hr1, hr1le⟩ := gradedNestC_pos_le hC (vertexFaceCounts k) (k + 1) _ hg2 hg21
  have hr2 : 0 < spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1G Cg alpha (alpha / 2) k) ∧
      spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1G Cg alpha (alpha / 2) k) ≤ 1 := by
    unfold spectrumPieceRho singlePieceGlobalRho1G
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
  unfold singlePieceGlobalDensityG singlePieceDensity
  calc singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (singlePieceGlobalRho1G Cg alpha (alpha / 2) k)) 1 *
        singlePieceGlobalC Qb alpha (alpha / 2) k (singlePieceGlobalC Qb alpha (alpha / 2) k
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (singlePieceGlobalRho1G Cg alpha (alpha / 2) k)) 1)) ≤ 1 * 1 :=
        mul_le_mul ht1 hc2le hc2.le zero_le_one
    _ = 1 := one_mul 1

end LeanProofs.GowersSzemeredi
