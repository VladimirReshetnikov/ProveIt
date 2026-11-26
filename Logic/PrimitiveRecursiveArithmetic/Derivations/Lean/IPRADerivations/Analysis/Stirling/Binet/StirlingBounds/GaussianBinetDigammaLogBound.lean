import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalPrefix
import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianLogGammaEulerDigammaFractionsCofinal
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Recurrence.GaussianLogGammaEulerTerminalShiftError
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# The complex digamma differs from the canonical logarithm by at most 1/Re z

Choose one cutoff in the literal Euler slope and in the logarithm increment.
The shifted logarithm approaches the finite slope's terminal real logarithm,
while the reciprocal rectangle errors telescope to 1/Re z. Removing the
dyadic allowances gives the bound on the original C27 digamma evaluator.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetDigammaLogBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetReciprocalPrefix (sample)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (shifted_source)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNameEquivalence (point_at cross_refl cross_symm)
open GaussianNamedDifference (sample_error)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder
  (distance_congr distance_radius_mono distance_symmetric distance_triangle_same reversed_difference)
open GaussianRationalHorner (canonical positive_product qadd qzero)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "S" => GaussianLogGammaEulerReciprocalSlope.nameF
local notation "sd" => GaussianLogGammaEulerReciprocalSlope.data
local notation "C" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "cd" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "F" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "fd" => GaussianLogGammaEulerDigammaFractionsCofinal.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem log_change (p A B D neg N : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] distanceBounded (qsub (sample p A B D neg N) (ap2 L p (ld A B D neg)))
      (reciprocalSum A B D neg N) (D*unit p+num 5*A) (A*unit p) := by
  let E := A+N*D
  let U := unit p
  let t := GaussianFastValueCut.exponent (num 8*N+one) p
  let V := unit t
  let x := ld E B D neg
  let y := ld A B D neg
  let a := ap2 L p x
  let b := ap2 L p y
  let c := ap2 L t x
  let d := ap2 L t y
  let sum := reciprocalSum A B D neg N
  have hA := h.andE₁.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have hAU := positive_product A U hA hU
  have hUV := positive_product U V hU hV
  have hbudget : Γ ⊢[PRAAx] le ((num 8*N+one)*U) V :=
    GaussianFastValueCut.query_budget _ _
  have hbase : Γ ⊢[PRAAx] le U ((num 8*N+one)*U) := by ipra_le 8*𝔞(N)*𝔞(U)
  have hcost : Γ ⊢[PRAAx] le (num 8*N*U) ((num 8*N+one)*U) := by ipra_le 𝔞(U)
  have hu := le_trans hbase hbudget
  have hpay := le_trans hcost hbudget
  have hleft : Γ ⊢[PRAAx] distanceBounded a c two U :=
    distance_radius_mono _ _ _ _ _ _ hUV hU (by ipra_le 𝔞(U)*sl hu)
      (point_at L x p t (GaussianRightHalfPlaneLogarithm.regular E B D neg (shifted_source N A D neg h)))
  have hright : Γ ⊢[PRAAx] distanceBounded b d two U :=
    distance_radius_mono _ _ _ _ _ _ hUV hU (by ipra_le 𝔞(U)*sl hu)
      (point_at L y p t (GaussianRightHalfPlaneLogarithm.regular A B D neg h))
  have clocks := GaussianFastValueCut.distance_difference_same a b c d two two U hU hleft hright
  have first : Γ ⊢[PRAAx] distanceBounded (qsub a b) (qsub c d) (num 4*A) (A*U) :=
    distance_radius_mono _ _ _ _ _ _ hU hAU (by ipra_le 0) clocks
  have prefixBound := GaussianBinetReciprocalPrefix.prefix_error t A B D neg N h
  have raw : Γ ⊢[PRAAx] distanceBounded (qsub c d) sum (D*U+A) (A*U) := by
    have mono : Γ ⊢[PRAAx] le
        (GaussianBinetReciprocalPrefix.numerator t A D N*(A*U))
        ((D*U+A)*GaussianBinetReciprocalPrefix.denominator t A D N) := by
      change Γ ⊢[PRAAx] le ((D*D*N*V+num 8*N*(A*E))*(A*U)) ((D*U+A)*(A*E*V))
      dsimp only [E]
      ipra_le 𝔞(A)^2*𝔞(D)*𝔞(U)*𝔞(V)+𝔞(A)^2*𝔞(A+N*D)*sl hpay
    exact distance_congr (qsub_congr (.eqRefl _) (GaussianBinetReciprocalPrefix.base_sample t A B D neg))
      (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ _ _ (GaussianBinetReciprocalPrefix.denominator_positive t A D neg N h)
        hAU mono prefixBound)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same (qsub a b) (qsub c d) sum _ _ (A*U) hAU first raw)

private theorem double_subtract (a b : PTm n) (hb : Γ ⊢[PRAAx] canonical b) :
    Γ ⊢[PRAAx] qsub a (qsub a b) ≐ b := by
  have opposite : Γ ⊢[PRAAx] qsub qzero a ≐ qnegative a :=
    (qadd_commutative _ _).eqTrans (qadd_zero_right _ (GaussianRationalMetric.qnegative_canonical a))
  have cancel := (qadd_congr (.eqRefl a) opposite.eqSymm).eqTrans (GaussianNameRingLaws.additive_inverse_value a)
  change Γ ⊢[PRAAx] qadd a (qnegative (qsub a b)) ≐ b
  have reorder : Γ ⊢[PRAAx] qadd a (qadd b (qnegative a)) ≐ qadd b (qadd a (qnegative a)) :=
    (GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
      ((qadd_congr (qadd_commutative a b) (.eqRefl (qnegative a))).eqTrans
        (GaussianRationalSumAlgebra.qadd_associative _ _ _))
  exact (qadd_congr (.eqRefl a) (reversed_difference a b)).eqTrans
    (reorder.eqTrans ((qadd_congr (.eqRefl b) cancel).eqTrans (qadd_zero_right b hb)))

private theorem diagonal (p A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    distanceBounded (ap2 C p (cd A B D neg)) (ap2 L p (ld A B D neg))
      (diagonalNumerator D A (num 23) p) (diagonalDenominator A p) := by
  let U := unit p
  let r := radius A B
  let s := radius (A+D) B
  let M := num 8*s+one+(two*s+(r+one))*U
  let N := succ M
  let b := ap2 L p (ld A B D neg)
  let e := sample p A B D neg N
  let v := GaussianPositiveRationalLogarithm.data M one
  let a := ap2 logF p v
  let sum := reciprocalSum A B D neg N
  let co := ap2 C p (cd A B D neg)
  let fin := ap2 S p (sd A B D neg M)
  have hA := h.andE₁.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hAU := positive_product A U hA hU
  have hM : Γ ⊢[PRAAx] le one M := by unfold M; ipra_le 8*𝔞(s)+(2*𝔞(s)+𝔞(r)+1)*𝔞(U)
  have hlarge : Γ ⊢[PRAAx] le (num 8*s) M := by unfold M; ipra_le 1+(2*𝔞(s)+𝔞(r)+1)*𝔞(U)
  have hterm : Γ ⊢[PRAAx] le (two*s*U) M := by unfold M; ipra_le 8*𝔞(s)+1+(𝔞(r)+1)*𝔞(U)
  have hco : Γ ⊢[PRAAx] le ((r+one)*U) M := by unfold M; ipra_le 8*𝔞(s)+1+2*𝔞(s)*𝔞(U)
  have hMU := positive_product M U hM hU
  have first : Γ ⊢[PRAAx] distanceBounded co fin (num 3*A) (A*U) := by
    have bound := diagonal_rate C S (cd A B D neg) (sd A B D neg M) (r+one) M p hM
      (GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_cutoff_rate A B D neg M h hM)
    exact distance_radius_mono _ _ _ _ _ _ hMU hAU (by ipra_le 𝔞(A)*𝔞(U)*sl hco) bound
  have second : Γ ⊢[PRAAx] distanceBounded fin (qsub a sum) (num 6*A) (A*U) := by
    have bound := sample_error logF constantF v sum p
      (GaussianPositiveRationalLogarithm.name_regular M one (.andI hM (le_refl one))) (constant_regular sum)
    exact distance_radius_mono _ _ _ _ _ _ hU hAU (by ipra_le 0)
      (distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p sum)) (.eqRefl _) (.eqRefl _) bound)
  have third : Γ ⊢[PRAAx] distanceBounded a e (num 9*A) (A*U) :=
    distance_symmetric _ _ _ _ hAU (distance_radius_mono _ _ _ _ _ _ hMU hAU
      (by ipra_le 𝔞(A)*𝔞(U)*sl hterm)
      (GaussianLogGammaEulerTerminalShiftError.terminal_sample_error p A B D neg M h hlarge))
  have fourth := distance_symmetric _ _ _ _ hAU (log_change p A B D neg N h)
  have last := GaussianFastValueCut.distance_difference_same a sum e (qsub e b) _ _ (A*U) hAU third fourth
  have middle := distance_triangle_same co fin (qsub a sum) _ _ (A*U) hAU first second
  have chain := distance_triangle_same co (qsub a sum) (qsub e (qsub e b)) _ _ (A*U) hAU middle last
  have hb : Γ ⊢[PRAAx] canonical b := GaussianNameArithmetic.add_canonical _ _ _ _ p
  exact distance_congr (.eqRefl _) (double_subtract e b hb)
    (by unfold diagonalNumerator; ipra_ring) (.eqRefl _) chain

theorem independent_rate (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] independentRate F L (fd A B D neg) (ld A B D neg) D A := by
  have logRegular := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have slopeRegular := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D neg h
  have equivalent := GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent A B D neg h
  have envelope : Γ ⊢[PRAAx] diagonalEnvelope C L (cd A B D neg) (ld A B D neg) D A (num 23) := by
    refine .allI ?_
    let s (w : PTm n) := Syn.shift w
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s neg) :=
      by simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
    simpa only [diagonalEnvelope, s, Syn.shift, GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData, GaussianLogGammaEulerReciprocalSlopeCofinal.subst_data,
      GaussianLogGammaEulerResidualRadius.subst_radius,
      GaussianRightHalfPlaneLogarithm.subst_data, PTm.subst_num] using
      diagonal (var 0) (s A) (s B) (s D) (s neg) hs
  exact GaussianNamedRateTransport.transport C L F L _ _ _ _ D A h.andE₁.andE₁
    (GaussianNamedLipschitzRate.independent_rate C L _ _ D A (num 23) h.andE₁.andE₁
      slopeRegular logRegular envelope)
    (cross_symm C F _ _ equivalent) (cross_refl L _ logRegular)

theorem actual_complex_digamma_logarithm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 2) (var 3) ⟶ independentRate F L
      (fd (var 0) (var 1) (var 2) (var 3)) (ld (var 0) (var 1) (var 2) (var 3)) (var 2) (var 0)) :=
  closeUniv 4 (.impI (independent_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetDigammaLogBound
