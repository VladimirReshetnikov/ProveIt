import GowersSzemeredi.Proofs16SinglePieceGlobal
import GowersSzemeredi.Proofs16SinglePieceFrequency

/-! A dense multilinear frequency box from global-to-local covers (Notes L.1
repair).

The scale conditions of `single_piece_lift_global` are packaged as
`SinglePieceGlobalScale`, with the final density
`singlePieceGlobalDensity` and the final width `singlePieceGlobalWidth`.
* `single_piece_lift_global'` restates the lift with this packaging.
* `single_piece_frequency_box_global`: let `f` not be uniform of degree
  `k + 2`. Then some proper box `P ⊆ (ℤ/N)^(k+1)` and one multilinear `μ` have
  `singlePieceGlobalDensity·|P|` large-frequency points. The inputs are
  `PolyCoverAt l` for `l ≤ k` and the retiled linearity bound. The chain:
  `section16_large_frequency_graph`, then explicit Lemma 15.6
  (`β = γ = α/2`), then `single_piece_lift_global` at `θ = α`, `γ = α/2`.

This is the satisfiable replacement for the vacuous
`single_piece_frequency_box`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The density after the remainder step. -/
def singlePieceGlobalRho1 (C : Real → Real) (theta gamma : Real) (k : Nat) : Real :=
  nestC (fun _ => C) (2 ^ k - 1) (globalTheta2 theta gamma k)

/-- The slice density control. -/
def singlePieceGlobalC (Qb : Nat → Real → Real → Real → Real) (theta gamma : Real) (k : Nat) :
    Real → Real :=
  fun s => s / 2 / Qb k gamma (globalBudget theta gamma k) (s / 2)

/-- The final density. -/
def singlePieceGlobalDensity (Qb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (theta gamma : Real) (k : Nat) : Real :=
  singlePieceDensity (singlePieceGlobalC Qb theta gamma k)
    (spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1 C theta gamma k)) 1

/-- The spectrum graph-count bound. -/
def singlePieceGlobalQmax (Qb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (theta gamma : Real) (k : Nat) : Real :=
  Qb k (section16Delta (section16ThetaOne theta gamma k)) (globalBudget theta gamma k)
    (singlePieceGlobalRho1 C theta gamma k / 2 / 2)

/-- The final width. -/
def singlePieceGlobalWidth (Qb Eb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (theta gamma : Real) (k : Nat) (eps : Nat → Real) (m q : Nat) : Nat :=
  Nat.sqrt (coverWidth (Eb k gamma (globalBudget theta gamma k))
    (singlePieceGlobalC Qb theta gamma k
      (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (singlePieceGlobalRho1 C theta gamma k)) 1))
    (coverWidth (Eb k gamma (globalBudget theta gamma k))
      (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
        (singlePieceGlobalRho1 C theta gamma k)) 1)
      ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊) - 1) - 1

/-- The scale conditions at one modulus. -/
def SinglePieceGlobalScale (Qb Eb : Nat → Real → Real → Real → Real) (C : Real → Real)
    (W : Real → Nat → Nat) (theta gamma : Real) (k : Nat) (eps : Nat → Real)
    (thr : Nat → Nat) (N m : Nat) : Prop :=
  4 ≤ nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) (globalTheta2 theta gamma k) N ∧
  1 ≤ m ∧
  m ≤ coverWidth (Eb k (section16Delta (section16ThetaOne theta gamma k))
      (globalBudget theta gamma k))
    (singlePieceGlobalRho1 C theta gamma k / 2)
    ⌈(nestW (fun _ => C) (fun _ => W) (2 ^ k - 1) (globalTheta2 theta gamma k) N : Real) / 8⌉₊ ∧
  ∀ q : Nat, (q : Real) ≤ singlePieceGlobalQmax Qb C theta gamma k →
    thr q ≤ m ∧ 4 ≤ spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
    2 ≤ spectrumPieceRho (fun t => t / 2) (singlePieceGlobalRho1 C theta gamma k) ^ 3 *
      spectrumCellWidth (section16Zeta theta gamma k) m (eps q) ∧
    2 ≤ coverWidth (Eb k gamma (globalBudget theta gamma k))
        (singlePieceGlobalC Qb theta gamma k
          (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
            (singlePieceGlobalRho1 C theta gamma k)) 1))
      (coverWidth (Eb k gamma (globalBudget theta gamma k))
        (singlePieceTheta (spectrumPieceRho (fun t => t / 2)
          (singlePieceGlobalRho1 C theta gamma k)) 1)
        ⌈spectrumCellWidth (section16Zeta theta gamma k) m (eps q) / 8⌉₊)

/-- **The single-piece lift from global-to-local covers**, packaged. -/
theorem single_piece_lift_global' {k : Nat} (hk : 1 ≤ k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {Qb Eb : Nat → Real → Real → Real → Real}
    (hcov : ∀ l, 1 ≤ l → l ≤ k → PolyCoverAt l (Qb l) (Eb l))
    (hQb : ∀ l g t s, 0 < s → s ≤ 1 → 1 ≤ Qb l g t s)
    (hEb : ∀ l g t s, 0 < s → s ≤ 1 → 0 < Eb l g t s)
    {C : Real → Real} {W : Real → Nat → Nat}
    (hC : ∀ t, 0 < t → t ≤ 1 → 0 < C t ∧ C t ≤ 1) (hW : ∀ t, Monotone (W t))
    (hCle : ∀ l, 1 ≤ l → l ≤ k → ∀ t, C t ≤ (liftLastC^[k + 1 - l]
      (fun s => s / 2 / Qb l gamma (globalBudget theta gamma k) (s / 2))) t)
    (hWle : ∀ l, 1 ≤ l → l ≤ k → ∀ t L, W t L ≤ (liftLastW^[k + 1 - l]
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
    (hscale : SinglePieceGlobalScale Qb Eb C W theta gamma k eps thr N m) :
    ∃ q : Nat, (q : Real) ≤ singlePieceGlobalQmax Qb C theta gamma k ∧
      ∃ (S : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        S.IsProper ∧ IsMultilinear mu ∧
        singlePieceGlobalWidth Qb Eb C theta gamma k eps m q ≤ S.width ∧
        singlePieceGlobalDensity Qb C theta gamma k * S.carrier.card ≤
          (B.filter fun z => z ∈ S.carrier ∧ phi z = mu z).card := by
  obtain ⟨hL4, hm1, hm, hpar⟩ := hscale
  exact single_piece_lift_global hk ht ht1 hg hg1 hcov hQb hEb hC hW hCle hWle eps thr hretile
    B phi hB hprodB hL4 m hm1 hm hpar

/-- **A dense multilinear frequency box from global-to-local covers.** -/
theorem single_piece_frequency_box_global {k : Nat} (hk : 1 ≤ k) {alpha : Real}
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
    {N : Nat} [NeZero N] [Fact N.Prime] (hodd : Odd N)
    (hN : lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤ (N : Real)) (m : Nat)
    (hscale : SinglePieceGlobalScale Qb Eb C W alpha (alpha / 2) k eps thr N m)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha (k + 2)) :
    ∃ q : Nat, (q : Real) ≤ singlePieceGlobalQmax Qb C alpha (alpha / 2) k ∧
      ∃ (P : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
        P.IsProper ∧ IsMultilinear mu ∧
        singlePieceGlobalWidth Qb Eb C alpha (alpha / 2) k eps m q ≤ P.width ∧
        singlePieceGlobalDensity Qb C alpha (alpha / 2) k * P.carrier.card ≤
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
  obtain ⟨q, hq, S, mu, hS, hmu, hSw, hcount⟩ := single_piece_lift_global' hk ha ha1 hg hg1
    hcov hQb hEb hC hW hCle hWle eps thr hretile B' phi hB (hprod.mono hB'B) m hscale
  refine ⟨q, hq, S, mu, hS, hmu, hSw, hcount.trans ?_⟩
  unfold section16LargeMultilinearFrequencyCount countWhere
  exact_mod_cast Finset.card_le_card fun z hz => by
    obtain ⟨hzB', hzS, hzmu⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzS, ?_⟩
    rw [← hzmu]
    exact hfreq z (hB'B hzB')

end LeanProofs.GowersSzemeredi
