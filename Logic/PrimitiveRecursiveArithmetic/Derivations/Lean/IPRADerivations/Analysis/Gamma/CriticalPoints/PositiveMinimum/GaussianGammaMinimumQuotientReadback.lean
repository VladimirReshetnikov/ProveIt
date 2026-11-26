import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianRationalInvertibleNorm

/-!
# Recovering a small difference from its divided-difference bound

The original divided-difference samples are small when their regular
name is close to zero. Multiplying the raw quotient by the exact
nonzero increment recovers the original difference. A bound `A/B` on
that increment multiplies the leading radius by exactly `A/B`,
with the ordinary independent observation errors at the endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumQuotientReadback

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedDifferenceQuotient
  (nameF data input raw inverse numerator denominator denominator_positive independent_readback actual_inverse)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator independent_rate)
open GaussianNameRingLaws (zeroF zero_at)
open GaussianRationalHorner (qmul ofGaussian qzero positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded qsub_canonical)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianReconstructionRoots (norm_from_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" u:max => Groth.ι (Q.mk Γ u)

def diagonalCost (A D : PTm n) : PTm n := A*(num 3+two*D)

ipra_subst diagonalCost [two]

private theorem raw_norm (F G : PR 2) (x y h D z C N t : PTm n)
    (hQ : Γ ⊢[PRAAx] input F G x y h D) (hN : Γ ⊢[PRAAx] le one N)
    (small : Γ ⊢[PRAAx] independentRate (nameF F G) zeroF (data F G x y h D) z C N) :
    Γ ⊢[PRAAx] bounded (raw F G t t x y h D)
      (diagonalNumerator C N (num 3+two*D) t) (diagonalDenominator N t) := by
  let U := unit t
  let first := raw F G t t x y h D
  let second := ap2 (nameF F G) t (data F G x y h D)
  have hu := unit_positive (Γ := Γ) t
  have hn := positive_product N U hN hu
  have small' : Γ ⊢[PRAAx] distanceBounded second qzero (C*U+two*N) (N*U) :=
    distance_congr (.eqRefl _) (zero_at t z) (.eqRefl _) (.eqRefl _)
      (diagonal_rate _ _ _ _ _ _ t hN small)
  have read := distance_symmetric _ _ _ _ (denominator_positive t t t)
    (independent_readback F G t t t x y h D hQ)
  have read' : Γ ⊢[PRAAx] distanceBounded first second (one+two*D) U :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive t t t) hu
      (le_congr (by unfold numerator denominator U; ipra_ring) (.eqRefl _) (le_refl _)) read
  have bound := norm_from_distance first second (one+two*D) U (C*U+two*N) (N*U) hu hn
    read' ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hn).iffMp small')
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hu hn) hn
    (le_congr (by unfold diagonalNumerator diagonalDenominator U; ipra_ring) (.eqRefl _) (le_refl _)) bound

theorem endpoint_diagonal (F G : PR 2) (x y h D z A B C N t : PTm n)
    (hQ : Γ ⊢[PRAAx] input F G x y h D) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (step : Γ ⊢[PRAAx] bounded (ofGaussian h D) A B)
    (small : Γ ⊢[PRAAx] independentRate (nameF F G) zeroF (data F G x y h D) z C N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F t x) (ap2 G t y)
      (diagonalNumerator (A*C) (B*N) (diagonalCost A D) t) (diagonalDenominator (B*N) t) := by
  let rawPoint := raw F G t t x y h D
  let stepPoint := ofGaussian h D
  let endpointDifference := qsub (ap2 F t x) (ap2 G t y)
  have rev := (GaussianRationalPowerAlgebra.qmul_commutative stepPoint (inverse h D)).eqTrans
    (actual_inverse h D hQ.andE₂.andE₂)
  have e : Γ ⊢[PRAAx] qmul stepPoint rawPoint ≐ endpointDifference :=
    GaussianRationalInvertibleNorm.qmul_roundtrip stepPoint (inverse h D) endpointDifference rev (qsub_canonical _ _)
  have npos := positive_product _ _ hN (unit_positive t)
  have prod := bounded_product _ _ _ _ _ _ hB npos step (raw_norm F G x y h D z C N t hQ hN small)
  have both := positive_product _ _ hB npos
  have width := positive_product _ _ (positive_product _ _ hB hN) (unit_positive t)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ both width
    (by
      dsimp only [diagonalNumerator,diagonalDenominator,diagonalCost]
      ipra_le 𝔞(A)*𝔞(num 3+two*D)*𝔞(B)*𝔞(N)^2*𝔞(unit t)*sl hB)
    (bound_congr e (.eqRefl _) (.eqRefl _) prod)

theorem original_endpoint_rate (F G : PR 2) (x y h D z A B C N : PTm n)
    (hQ : Γ ⊢[PRAAx] input F G x y h D) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (step : Γ ⊢[PRAAx] bounded (ofGaussian h D) A B)
    (small : Γ ⊢[PRAAx] independentRate (nameF F G) zeroF (data F G x y h D) z C N) :
    Γ ⊢[PRAAx] independentRate F G x y (A*C) (B*N) := by
  apply independent_rate F G x y (A*C) (B*N) (diagonalCost A D)
    (positive_product _ _ hB hN) hQ.andE₁ hQ.andE₂.andE₁
  let s (w : PTm n) := Syn.shift w
  let Δ := Γ.map Fm.shift
  have hQ' : Δ ⊢[PRAAx] input F G (s x) (s y) (s h) (s D) := by simpa [Δ,s,Fm.shift,Syn.shift] using hQ.shift
  have hN' : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift
  have hB' : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift
  have hs' : Δ ⊢[PRAAx] bounded (ofGaussian (s h) (s D)) (s A) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using step.shift
  have hr' : Δ ⊢[PRAAx] independentRate (nameF F G) zeroF (data F G (s x) (s y) (s h) (s D)) (s z) (s C) (s N) :=
    by simpa [Δ,s,Fm.shift,Syn.shift] using small.shift
  refine .allI ?_
  simpa only [diagonalEnvelope, Syn.shift, s, subst_diagonalCost, PTm.subst_mul] using
    endpoint_diagonal F G (s x) (s y) (s h) (s D) (s z) (s A) (s B) (s C) (s N) (var 0) hQ' hN' hB' hs' hr'

theorem original_bounded_divided_difference_endpoints_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((input F G (var 0) (var 1) (var 2) (var 3) ⋏
        (le one (var 8) ⋏ (le one (var 6) ⋏
          (bounded (ofGaussian (var 2) (var 3)) (var 5) (var 6) ⋏
            independentRate (nameF F G) zeroF (data F G (var 0) (var 1) (var 2) (var 3))
              (var 4) (var 7) (var 8))))) ⟶
        independentRate F G (var 0) (var 1) (var 5*var 7) (var 6*var 8)) :=
  closeUniv 9 (.impI (original_endpoint_rate F G _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumQuotientReadback
