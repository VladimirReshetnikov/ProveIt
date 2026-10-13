import GowersSzemeredi.Proofs16WithLemma6
import GowersSzemeredi.Proofs16Lemma9

/-! Lemma 16.9 with arbitrary control functions for the spectrum.

The spectrum count `qDelta` enters the Lemma 16.9 width only through the
Lemma 16.1 exponent `K^(-2^(k+1)*qDelta)`. Here it is bounded by
`Qb (sigma/2)` and the spectrum exponent is `Eb (sigma/2)`, so a
loss-independent spectrum count gives a width exponent that is polynomial in
the loss. The remainder (`gamma`-side) cover is unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Lemma 16.9 uniformly over proper boxes and losses, with arbitrary
spectrum controls `Qb`, `Eb` evaluated at half the loss. -/
def Section16AllBoxLineCoversWith {N k : Nat} [NeZero N]
    (theta gamma : Real) (Qb Eb : Real → Real) (B1 : Finset (Point N (k + 1)))
    (phi1 : Point N (k + 1) → ZMod N) : Prop :=
  ∀ sigma : Real, 0 < sigma → sigma ≤ 1 → ∀ m : Nat,
    ∀ P : Box N (k + 1), P.IsProper → m ≤ P.width →
      ∃ qGamma qDelta : Nat,
        (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
        (qDelta : Real) ≤ Qb (sigma / 2) ∧
        Section16LineCover P B1 phi1 sigma
          (lemma9WidthWith m qDelta k sigma theta gamma (Eb (sigma / 2))
            (section16Zeta theta gamma k))
          qGamma

theorem section16_all_box_line_covers_with :
  ∀ (N k : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (Qb Eb : Real → Real),
      (∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1) →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N) (x0 : Point N k),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    let r := section16Lemma9R theta gamma k
    let B1 := section16GoodDomain B H1 Y x0
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    Section16PhiOneIdentity B1 phi x0 phiPrime →
    MultiplyLinearFunction gamma r B1 (section16PhiRemainder phi x0) →
    Section16AllBoxLineCoversWith theta gamma Qb Eb B1 (section16PhiOne phi x0) := by
  intro N k _ _ hk theta gamma ht ht1 hg hg1 Qb Eb hQE B phi H Jbase H1 Y phiPrime x0
  dsimp only
  intro hH1 hML hselection hidentity hrem
  intro sigma hs hs1 m P hP hmP
  have hs2 : 0 < sigma / 2 := by positivity
  obtain ⟨hQ, ha, ha1⟩ := hQE (sigma / 2) hs2 (by linarith)
  exact proper_lemma_16_9_with N k m hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime x0 hH1 hML hselection hidentity hrem P hP hmP

end LeanProofs.GowersSzemeredi
