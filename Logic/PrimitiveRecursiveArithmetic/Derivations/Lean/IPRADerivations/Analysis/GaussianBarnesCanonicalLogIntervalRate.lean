import IPRADerivations.Analysis.GaussianBarnesCanonicalFiniteLog

/-!
# Compare two rounded Barnes log intervals at one clock

The common rows cancel exactly. The remaining rounded rows pay the
computed rounding budget and have the original (2R^3/(3N)) tail
radius at their actual starting index.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogIntervalRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalFiniteLog (gain)
open GaussianBarnesCanonicalLogRow (boundNumerator)
open GaussianBarnesCanonicalLogTail (source tailDenominator tail_bound tail_denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReconstructionRoots (norm_from_distance)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "value" => GaussianBarnesCanonicalLogRoundedTail.value
local notation "roundUnit" => DyadicComplexLogarithm.unit

theorem source_later (z R B N M : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (leNM : Γ ⊢[PRAAx] le N M) : Γ ⊢[PRAAx] source z R B M :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ leNM)
    (.andI h.andE₂.andE₂.andE₁ (le_trans h.andE₂.andE₂.andE₂ leNM)))

theorem suffix_gain (N a b : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (monus b a*(two*((N+a)+monus b a))) (gain N b) := by
  let r := monus b a
  have sum : Γ ⊢[PRAAx] a+r ≐ b := (eq_add_of_le h).eqSymm
  have h1 := le_congr (.eqRefl r) sum (le_add_left r a)
  have endEq := (add_assoc N a r).eqTrans (congrAdd (.eqRefl N) sum)
  have h2 : Γ ⊢[PRAAx] le (two*(N+b)) (num 5*(N+b)) :=
    mul_le_mul_right (N+b) (le_of_eq_add (d := num 3) (by ipra_ring))
  exact le_mul_mono h1 (le_congr (congrMul (.eqRefl two) endEq).eqSymm (.eqRefl _) h2)

theorem ordered_difference (p v z R B N a b : PTm n) (hs : Γ ⊢[PRAAx] source z R B N)
    (hab : Γ ⊢[PRAAx] le a b) (paid : Γ ⊢[PRAAx] le (gain N b*unit p) (roundUnit v)) :
    Γ ⊢[PRAAx] distanceBounded (value v z R B N b) (value v z R B N a)
      (boundNumerator R*unit p+tailDenominator (N+a)) (tailDenominator (N+a)*unit p) := by
  let J := N+a
  let r := monus b a
  let W := tailDenominator J
  let U := unit p
  let C := boundNumerator R
  let x := value v z R B N a
  let w := value v z R B N b
  let y := value v z R B J r
  let z' := GaussianBarnesCanonicalLogTail.value z B J r (DyadicComplexLogarithm.precision v)
  have sep := source_later z R B N J hs (le_add_right _ _)
  have hW := tail_denominator_positive J sep.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have fit := le_trans (mul_le_mul_right U (suffix_gain N a b hab)) paid
  have approx : Γ ⊢[PRAAx] distanceBounded y z' one U :=
    distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive v) hU
      (le_congr (.eqRefl _) (one_mul _).eqSymm fit)
      (GaussianBarnesCanonicalLogRoundedTail.rounding_error v z R B J r sep)
  have tailEstimate : Γ ⊢[PRAAx] bounded z' C W := tail_bound _ _ _ _ _ _ sep
  have combined : Γ ⊢[PRAAx] bounded y (C*U+W) (W*U) :=
    bound_congr (.eqRefl _) (by ipra_ring) (mul_comm _ _)
      (norm_from_distance y z' one U C W hU hW approx tailEstimate)
  have lengthEq : Γ ⊢[PRAAx] b ≐ a+r := eq_add_of_le hab
  have normalize : Γ ⊢[PRAAx] w ≐ value v z R B N (a+r) := by
    ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
      [.eqRefl _,.eqRefl _,.eqRefl _,.eqRefl _,.eqRefl _,lengthEq]
  have split : Γ ⊢[PRAAx] w ≐ GaussianRationalHorner.qadd x y :=
    normalize.eqTrans (GaussianBarnesCanonicalLogRoundedTail.split v z R B N a r)
  have hY := GaussianRationalFiniteSum.sum_canonical (Γ := Γ) GaussianBarnesCanonicalLogRoundedTail.body r
    (GaussianBarnesCanonicalLogRoundedTail.data v z R B J)
  exact bound_congr ((qsub_congr split (.eqRefl x)).eqTrans (qadd_sub_cancel x y hY)).eqSymm
    (.eqRefl _) (.eqRefl _) combined

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogIntervalRate
