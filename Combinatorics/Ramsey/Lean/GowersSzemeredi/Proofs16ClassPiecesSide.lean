import GowersSzemeredi.Proofs16ClassPieces
import GowersSzemeredi.Proofs16SinglePieceGlobalSide
import GowersSzemeredi.Proofs16Lemma5Side

/-! Declarations of `Proofs16ClassPieces` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- The spectrum parameter `δ(θ₁)`. -/
def classDelta (theta gamma : Real) (k : Nat) : Real :=
  section16Delta (section16ThetaOne theta gamma k)

/-- The class thresholds a piece needs: spectra at `(θ′, δ)`, faces and slices at `(θ′, γ)`. -/
def classPieceThr (Thr : Real → Real → Real) (theta gamma : Real) (k : Nat) : Real :=
  max (Thr (classBudget theta gamma k) (classDelta theta gamma k))
    (Thr (classBudget theta gamma k) gamma)

/-- The class thresholds of a piece, for power controls. -/
def classPieceThreshold (V : Real) (dT : Nat) (theta gamma : Real) (k : Nat) : Real :=
  max ((V * (2 / (classDelta theta gamma k * classBudget theta gamma k))) ^ dT)
    ((V * (2 / (gamma * classBudget theta gamma k))) ^ dT)

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **One `(k+1)`-dimensional piece over a uniform class**, from Lemma 15.6's
arrangements and the product property. -/
theorem class_piece_data {k : Nat} {Thr : Real → Real → Real}
    {Cnt Exp : Real → Real → Nat → Real → Real} (C : UniformClassWith k Thr Cnt Exp)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : classPieceThr Thr theta gamma k ≤ N)
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (hBG : partialGraph B phi ⊆ Gamma)
    (hBarr : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    Nonempty (ClassPiece C Gamma (section16Zeta theta gamma k) (classBudget theta gamma k)
      (classBudget theta gamma k) (classDelta theta gamma k) (classBudget theta gamma k) gamma) :=
  have hp := lemma_16_5_with_printed_hyps k ht ht1 hg hg1
  class_piece_data_with C hp.1 hp.2.1 hp.2.2 (by unfold section16Zeta; positivity) hg hg1
    hN Gamma B phi hBG hBarr hprodB

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem classBudget_pos_le {theta gamma : Real} (k : Nat) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < classBudget theta gamma k ∧ classBudget theta gamma k ≤ 1 := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le k ht ht1 hg hg1
  have h2 : (1 : Real) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num)
  unfold classBudget
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  linarith

end

end LeanProofs.GowersSzemeredi
