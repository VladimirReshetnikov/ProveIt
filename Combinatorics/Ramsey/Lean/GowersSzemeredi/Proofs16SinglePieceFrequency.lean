import GowersSzemeredi.Proofs16SinglePieceLift
import GowersSzemeredi.Proofs16FrequencySelection
import GowersSzemeredi.Proofs15ExplicitThresholds

/-! The single-piece lift, step 6 (Notes L.1): a dense multilinear frequency
box from local inputs only.

**Warning.** Its inputs include the box-local `LocalRelationCoverAt` and
`LocalMultilinearPieceAt`, false for growing widths (Notes L.2), so this
statement is vacuous. The global-to-local replacement goes through
`single_piece_lift_core`.

`single_piece_frequency_box` is a conditional replacement for
`section16_joint_frequency_box`. Take `f` that is not uniform of degree
`k + 2`. Then some proper box `P ⊆ (ℤ/N)^(k+1)` and one multilinear `μ` have
`ρ·|P|` points `y` at which `μ y` is a large Fourier frequency of the
iterated difference.
- `section16_joint_frequency_box` needs the cover-form `Theorem162At l` for
  `l ≤ k`, and its density is `exp(−poly)` (Notes K.4).
- Here `ρ = singlePieceDensity c (spectrumPieceRho c_R ρ₁) 1` is polynomial
  in `α` whenever the local inputs are.

The chain:
1. `section16_large_frequency_graph`: the frequency graph `(B, φ)` with the
   product property at `α/2`.
2. Lemma 15.6 with its explicit threshold
   (`lemma_15_6_of_density_lower_all_explicit`, `β = γ = α/2`). Its
   arrangement parameter `(βγ/2)^E` is exactly
   `section16ThetaOne α (α/2) k`, and Lemma 16.4's dichotomy is not needed.
3. `single_piece_lift`, with vertex providers from the lower-dimensional
   inputs (`vertex_providers_of_low`).
4. The agreement points are large frequencies.

The output feeds `polynomial_localization_of_dense_frequency_box`
unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem two_inv_pow_44_eq_rpow : (2 : Real)⁻¹ ^ 44 = (2 : Real) ^ (-(44 : Real)) := by
  rw [Real.rpow_neg (by norm_num), inv_pow]
  congr 1
  exact_mod_cast (Real.rpow_natCast (2 : Real) 44).symm

/-- **A dense multilinear frequency box from local inputs.** -/
theorem single_piece_frequency_box {k : Nat} (hk : 1 ≤ k) {alpha : Real}
    (ha : 0 < alpha) (haHalf : alpha ≤ 1 / 2)
    {Qc : Real → Nat → Real} {cR : Real → Real} {wR : Real → Nat → Nat}
    {c : Real → Real} {w : Real → Nat → Nat} {C : Real → Real} {W : Real → Nat → Nat}
    {cl : Nat → Real → Real} {wl : Nat → Real → Nat → Nat}
    (hcover : LocalRelationCoverAt k
      (section16Delta (section16ThetaOne alpha (alpha / 2) k)) Qc cR wR)
    (hcR : ∀ t, 0 < t → t ≤ 1 → 0 < cR t ∧ cR t ≤ 1) (hwR : ∀ t, Monotone (wR t))
    (hslprov : LocalMultilinearPieceAt k (alpha / 2) c w)
    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))
    (hlow : ∀ l, 1 ≤ l → l ≤ k → LocalMultilinearPieceAt l (alpha / 2) (cl l) (wl l))
    (hcl : ∀ l t, 0 < t → t ≤ 1 → 0 < cl l t ∧ cl l t ≤ 1) (hwl : ∀ l t, Monotone (wl l t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, C t ≤ (liftLastC^[k + 1 - l] (cl l)) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, W t L ≤ (liftLastW^[k + 1 - l] (wl l)) t L)
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (eps : Nat → Real) (thr : Nat → Nat)
    (hretile : ∀ q, Section16RetiledLinearityBound k q (eps q) (thr q))
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real))
    (hL4 : 4 ≤ liftRemainderWidth C W alpha (alpha / 2) k N)
    (m : Nat) (hm1 : 1 ≤ m)
    (hm : m ≤ wR (liftRemainderRho C alpha (alpha / 2) k / 2)
      ⌈(liftRemainderWidth C W alpha (alpha / 2) k N : Real) / 8⌉₊)
    (hpar : ∀ q : Nat, (q : Real) ≤ Qc (liftRemainderRho C alpha (alpha / 2) k / 2)
        ⌊(section16Delta (section16ThetaOne alpha (alpha / 2) k)) ^ (-(2 : Int))⌋₊ →
      thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta alpha (alpha / 2) k) m (eps q) ∧
      2 ≤ spectrumPieceRho cR (liftRemainderRho C alpha (alpha / 2) k) ^ 3 *
        spectrumCellWidth (section16Zeta alpha (alpha / 2) k) m (eps q) ∧
      2 ≤ w (c (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C alpha (alpha / 2) k)) 1))
        (w (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C alpha (alpha / 2) k)) 1)
          ⌈spectrumCellWidth (section16Zeta alpha (alpha / 2) k) m (eps q) / 8⌉₊))
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ q : Nat, (q : Real) ≤ Qc (liftRemainderRho C alpha (alpha / 2) k / 2)
        ⌊(section16Delta (section16ThetaOne alpha (alpha / 2) k)) ^ (-(2 : Int))⌋₊ ∧
      ∃ (P : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        P.IsProper ∧ IsMultilinear mu ∧
        Nat.sqrt (w (c (singlePieceTheta
            (spectrumPieceRho cR (liftRemainderRho C alpha (alpha / 2) k)) 1))
          (w (singlePieceTheta (spectrumPieceRho cR (liftRemainderRho C alpha (alpha / 2) k)) 1)
            ⌈spectrumCellWidth (section16Zeta alpha (alpha / 2) k) m (eps q) / 8⌉₊) - 1) - 1 ≤
          P.width ∧
        singlePieceDensity c (spectrumPieceRho cR (liftRemainderRho C alpha (alpha / 2) k)) 1 *
            P.carrier.card ≤
          section16LargeMultilinearFrequencyCount f P mu alpha := by
  have ha1 : alpha ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := by positivity
  have hg1 : alpha / 2 ≤ 1 := by linarith
  -- 1. the frequency graph
  obtain ⟨B, phi, hBmass, hprod, hfreq⟩ :=
    section16_large_frequency_graph (k := k + 1) alpha ha ha1 f hf hnot
  -- 2. Lemma 15.6 with its explicit threshold
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
  have hprod' : HasProductProperty B' phi (alpha / 2) := hprod.mono hB'B
  -- 3. the single-piece lift
  obtain ⟨q, hq, S, mu, hS, hmu, hSw, hcount⟩ := single_piece_lift hk ha ha1 hg hg1 hcover hcR
    hwR hslprov hc hw hC hW eps thr hretile B' phi hB hprod'
    (vertex_providers_of_low hlow hcl hwl hCle hWle hprod') hL4 m hm1 hm hpar
  refine ⟨q, hq, S, mu, hS, hmu, hSw, hcount.trans ?_⟩
  -- 4. agreement points are large frequencies
  unfold section16LargeMultilinearFrequencyCount countWhere
  exact_mod_cast Finset.card_le_card fun z hz => by
    obtain ⟨hzB', hzS, hzmu⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzS, ?_⟩
    rw [← hzmu]
    exact hfreq z (hB'B hzB')

end LeanProofs.GowersSzemeredi
