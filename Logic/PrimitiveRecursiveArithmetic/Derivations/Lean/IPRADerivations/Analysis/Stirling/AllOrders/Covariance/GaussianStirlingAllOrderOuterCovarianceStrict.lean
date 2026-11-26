import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderOuterCovarianceRate

/-!
# A fixed positive lower bound for the covariance gap

An explicit lower bound for the first-panel margin exceeds the uniform
mesh error once S passes a primitive-recursive threshold. The remaining
margin is independent of the outer prefix length and of further refinements.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderOuterCovarianceStrict

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderBernoulliMeshMargin (coarseDen)
open GaussianStirlingAllOrderBoxProductGap (weightDenominator)
open GaussianStirlingAllOrderHalfGridMean (normalized_margin_positive)
open GaussianStirlingAllOrderOuterCovariance (firstMargin)
open GaussianStirlingAllOrderOuterCovarianceRate (gap meshBudget uniform_gap)
open RationalAlgebra (add_congr)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply negative order_of_representations)
open RationalFiniteSum (canonical_equal)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalNonnegativePowers (fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalSupMetric (numeratorOf denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def marginDenominator (m e : ℕ) (A B : PTm n) : PTm n :=
  num 32*coarseDen m*weightDenominator (num (e-1)) (A+B*ConciseIPRA.PTm.zero) B

def refinement (m e : ℕ) (A B : PTm n) : PTm n :=
  succ (marginDenominator m e A B*(numeratorOf (meshBudget m e A B)).pos)

theorem margin_den_positive (m e : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (marginDenominator m e A B) := by
  let U := A+B*ConciseIPRA.PTm.zero
  have hU : Γ ⊢[PRAAx] le one U := le_trans hA (le_add_right _ _)
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have base : Γ ⊢[PRAAx] le one (num 8*U+B) := le_trans (positive_product _ _ h8 hU) (le_add_right _ _)
  exact positive_product _ _
    (positive_product _ _ (by ipra_le 31) (GaussianStirlingAllOrderCenteredBernoulli.denominator_positive _ _ h8))
    (GaussianStirlingAllOrderPairedWeight.gap_denominator_positive _ _ _ _ base)

private theorem integer_cap (x : PTm n) :
    Γ ⊢[PRAAx] rationalLE x (fraction (numeratorOf x).pos one) := by
  let D := denominatorOf x
  let p := (numeratorOf x).pos
  let q := (numeratorOf x).neg
  have hd := RationalArgmin.denominator_positive (Γ := Γ) x
  apply order_of_representations _ _ (numeratorOf x) (ZT.ofNat p) D one
    (RationalRepresentations.represents_self x) (fraction_represents _ _ (le_refl one)) hd (le_refl one)
  apply zle_of_toZ (p*monus D one+q)
  have e := natEq (eq_add_of_le hd)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  dsimp only [p,q,D]
  ipra_simps
  linear_combination -𝔞((numeratorOf x).pos)*e

private theorem halve_fraction (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] add (fraction one (two*D)) (fraction one (two*D)) ≐ fraction one D := by
  let B := two*D
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ (le_succ_self one) hD
  apply canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _) (normalize_well_formed _ _ hD)
    (RationalRepresentations.represents_add _ _ _ _ _ _ (fraction_represents one B hB) (fraction_represents one B hB))
    (fraction_represents _ _ hD) (positive_product _ _ hB hB) hD
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  unfold B
  ipra_simps
  ring

theorem mesh_error_half_margin (m e : ℕ) (A B S : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le (refinement m e A B) S) :
    Γ ⊢[PRAAx] rationalLE (multiply (fraction one (S*num 4)) (meshBudget m e A B))
      (fraction one (two*marginDenominator m e A B)) := by
  let E := meshBudget m e A B
  let D := marginDenominator m e A B
  let p := (numeratorOf E).pos
  let N := S*num 4
  let c := fraction one N
  have ss := le_trans (zero_lt_succ (D*p)) hS
  have hn : Γ ⊢[PRAAx] le one N := positive_product _ _ ss (by ipra_le 3)
  have hd : Γ ⊢[PRAAx] le one (two*D) := positive_product _ _ (le_succ_self one) (margin_den_positive m e A B hA)
  have h := RationalArithmetic.multiply_monotone c _ _ (nonnegative_of_representation c one N hn (fraction_represents _ _ hn))
    (integer_cap E)
  have e := fraction_multiply (Γ := Γ) one N p one hn (le_refl one)
  have bound : Γ ⊢[PRAAx] le ((two*D)*(one*p)) (one*(N*one)) := by
    change Γ ⊢[PRAAx] le (succ (D*p)) S at hS
    unfold N
    ipra_le 2*sl hS + 2*𝔞 S + 2
  exact transitive (rationalLE_congr (.eqRefl _) e h) (fraction_order _ _ _ _ (positive_product _ _ hn (le_refl one)) hd bound)

theorem positive_gap (m e : ℕ) (he : 2≤e) (A B S L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] le (refinement m e A B) S) :
    Γ ⊢[PRAAx] rationalLE (fraction one (two*marginDenominator m e A B))
      (multiply (fraction two one) (gap m e A B S (succ (succ L)))) := by
  let U := A+B*ConciseIPRA.PTm.zero
  let D := marginDenominator m e A B
  let W := fraction one (two*D)
  let P := multiply (fraction two one) (gap m e A B S (succ (succ L)))
  have ss := le_trans (zero_lt_succ _) hS
  have hU : Γ ⊢[PRAAx] le one U := le_trans hA (le_add_right _ _)
  have hD := margin_den_positive m e A B hA
  have hW := positive_product _ _ (le_succ_self one) hD
  have h := normalized_margin_positive m (num (e-1)) U B hU hB
  have t := uniform_gap m e he A B S L hA hB ss
  have lower := transitive h (transitive t
    (add_monotone P P _ W (reflexive _) (mesh_error_half_margin m e A B S hA hS)))
  have turn := rationalLE_congr (halve_fraction D hD).eqSymm (.eqRefl _) lower
  have cancel := add_monotone _ _ (negative W) (negative W) turn (reflexive _)
  exact rationalLE_congr (add_negative_cancel W W (normalize_well_formed _ _ hW))
    (add_negative_cancel P W (RationalArithmetic.multiply_guard _ _)) cancel

theorem actual_original_outer_covariance_positive_gap_closed (m e : ℕ) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ le one (var 1) ⟶ le (refinement m e (var 0) (var 1)) (var 2) ⟶
        rationalLE (fraction one (two*marginDenominator m e (var 0) (var 1)))
          (multiply (fraction two one) (gap m e (var 0) (var 1) (var 2) (succ (succ (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.impI (positive_gap m e he _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderOuterCovarianceStrict
