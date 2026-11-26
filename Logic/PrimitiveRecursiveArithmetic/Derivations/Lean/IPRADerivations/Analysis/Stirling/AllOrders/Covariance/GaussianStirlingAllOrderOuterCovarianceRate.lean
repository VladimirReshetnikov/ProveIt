import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderMidpointPrefixRate
import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerIntegralCofinal

/-!
# One uniform mesh error for the strict outer covariance bound

The errors from the finite Bernoulli mean and the midpoint rows are
both bounded by one rational coefficient divided by 4S. The coefficient
depends on the encoded base and order, and is uniform in the outer prefix length.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderOuterCovarianceRate

open_ipra
open BernoulliBounds (bden bden_pos)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderFullGridMeanRate (correctedMean meanErrorNumerator meanErrorDenominator)
open GaussianStirlingAllOrderMidpointPrefixRate (midpointBudget uniform_midpoint_prefix)
open GaussianStirlingAllOrderOuterCovariance (firstMargin midpointPrefix strict_outer_prefix)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix panelPrefix)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderPowerIntegralPrefix (corrected_prefix_bounds)
open GaussianStirlingAllOrderPowerIntegralCofinal (terminal_primitive_bounds)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open RationalAlgebra (add_associative add_congr add_commutative multiply_negative multiply_add multiply_associative multiply_commutative multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply negative multiply_guard multiply_monotone)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalNormalForm (normalize_well_formed)
open RationalFiniteSum (canonical_equal sum_well_formed)
open RationalNonnegativePowers (fraction_multiply)
open RationalReciprocalPowerTail (add_zero_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "z" => fraction zero one

def massCap (e : ℕ) (A B : PTm n) : PTm n := add (primitive e A B) (fraction (power e B) one)
def meanCoefficient (m : ℕ) : PTm n := fraction (meanErrorNumerator m) (num (bden (2*(m+1))))
def meshBudget (m e : ℕ) (A B : PTm n) : PTm n :=
  add (multiply (meanCoefficient m) (massCap e A B)) (midpointBudget m e A B)

theorem uniform_mass_cap (e : ℕ) (he : 2≤e) (A B M L : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hM : Γ ⊢[PRAAx] le one M) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] rationalLE (massPrefix e A B M L) (massCap e A B) := by
  let W := massPrefix e A B M L
  have endpoint := (terminal_primitive_bounds e he A B L hA hL).andE₁
  have after := (corrected_prefix_bounds e he A B M L hA hM).andE₂
  have origin := rationalLE_congr (add_zero_right W (sum_well_formed _ _ _)) (.eqRefl _)
    (add_monotone W W z _ (reflexive _) endpoint)
  have bound := fraction_order (power e B) M (power e B) one hM (le_refl one) (by
    ipra_le Groth.ι (IPRA.Q.mk Γ (power e B))*sl hM)
  exact transitive (transitive origin after) (add_monotone _ _ _ _ (reflexive _) bound)

private theorem same_fraction (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] a*d ≐ c*b) : Γ ⊢[PRAAx] fraction a b ≐ fraction c d := by
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hb) (normalize_well_formed _ _ hd)
    (fraction_represents _ _ hb) (fraction_represents _ _ hd) hb hd
  apply ZT.derive
  simpa only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] using natEq h

private theorem double_mean_error (m : ℕ) (S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] multiply (fraction two one) (fraction (meanErrorNumerator m) (meanErrorDenominator m S)) ≐
      multiply (fraction one (S*num 4)) (meanCoefficient m) := by
  let a : PTm n := meanErrorNumerator m
  let D : PTm n := num (bden (2*(m+1)))
  let N := S*num 4
  let M := S*num 8
  have hD : Γ ⊢[PRAAx] le one D := Foundations.NumeralPrimes.num_le (bden_pos _)
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ hS (by ipra_le 3)
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have left := fraction_multiply two one a (D*M) (le_refl one) (positive_product _ _ hD hM)
  have right := fraction_multiply one N a D hN hD
  exact left.eqTrans ((same_fraction _ _ _ _ (positive_product _ _ (le_refl one) (positive_product _ _ hD hM))
    (positive_product _ _ hN hD) (by unfold M N; ipra_ring)).eqTrans right.eqSymm)

private theorem mean_split (m : ℕ) (S W : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] multiply (correctedMean m S) (multiply (fraction two one) W) ≐
      add (multiply (signedMean (m+1)) (multiply (fraction two one) W))
        (multiply (fraction one (S*num 4)) (multiply (meanCoefficient m) W)) := by
  let M : PTm n := signedMean (m+1)
  let a : PTm n := fraction (meanErrorNumerator m) (meanErrorDenominator m S)
  let c : PTm n := fraction two one
  let d := fraction one (S*num 4)
  let b : PTm n := meanCoefficient m
  have ea : Γ ⊢[PRAAx] multiply a (multiply c W) ≐ multiply d (multiply b W) :=
    (multiply_associative a c W).eqSymm.eqTrans
      ((multiply_congr ((multiply_commutative a c).eqTrans (double_mean_error m S hS)) (.eqRefl W)).eqTrans
        (multiply_associative d b W))
  exact (multiply_commutative (add M a) (multiply c W)).eqTrans
    ((multiply_add (multiply c W) M a).eqTrans
      (add_congr (multiply_commutative (multiply c W) M) ((multiply_commutative (multiply c W) a).eqTrans ea)))

noncomputable def uniformComparison (m e : ℕ) (A B S L : PTm n) : Fm PTm n :=
  let M := S*num 8
  let P := panelPrefix m (e-1) A B M L
  let W := massPrefix e A B M L
  rationalLE
    (add (multiply (fraction two one) P) (firstMargin m e A B))
    (add (multiply (signedMean (m+1)) (multiply (fraction two one) W))
      (multiply (fraction one (S*num 4)) (meshBudget m e A B)))

theorem uniform_outer_covariance (m e : ℕ) (he : 2≤e) (A B S L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] uniformComparison m e A B S (succ (succ L)) := by
  let M := S*num 8
  let K := succ (succ L)
  let W := massPrefix e A B M K
  let c := fraction one (S*num 4)
  let X := multiply (signedMean (m+1)) (multiply (fraction two one) W)
  let F := multiply (meanCoefficient m) (massCap e A B)
  let T := midpointBudget m e A B
  have hN : Γ ⊢[PRAAx] le one (S*num 4) := positive_product _ _ hS (by ipra_le 3)
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have hD : Γ ⊢[PRAAx] le one (num (bden (2*(m+1))) : PTm n) := Foundations.NumeralPrimes.num_le (bden_pos _)
  have hc := nonnegative_of_representation c one _ hN (fraction_represents _ _ hN)
  have hy := nonnegative_of_representation (meanCoefficient m) (meanErrorNumerator m) _ hD (fraction_represents _ _ hD)
  have Wcap := uniform_mass_cap e he A B M K hA hM (zero_lt_succ _)
  have cap := multiply_monotone c _ _ hc (multiply_monotone (meanCoefficient m) _ _ hy Wcap)
  have mid := uniform_midpoint_prefix m e he A B S L hA hS
  have sub := strict_outer_prefix m e (by omega) A B S (succ L) hA hB hS
  have algebra := (add_congr (mean_split m S W hS) (.eqRefl (midpointPrefix m e A B S K))).eqTrans
    (add_associative X (multiply c (multiply (meanCoefficient m) W)) (midpointPrefix m e A B S K))
  have finish := add_monotone X X _ _ (reflexive _)
    (rationalLE_congr (.eqRefl _) (multiply_add c F T).eqSymm (add_monotone _ _ _ _ cap mid))
  exact transitive (rationalLE_congr (.eqRefl _) algebra sub) finish

theorem actual_original_outer_covariance_uniform_rate_closed (m e : ℕ) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ le one (var 1) ⟶ le one (var 2) ⟶
        uniformComparison m e (var 0) (var 1) (var 2) (succ (succ (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (uniform_outer_covariance m e he _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

def gap (m e : ℕ) (A B S L : PTm n) : PTm n :=
  let M := S*num 8
  sub (multiply (signedMean (m+1)) (massPrefix e A B M L)) (panelPrefix m (e-1) A B M L)

theorem uniform_gap (m e : ℕ) (he : 2≤e) (A B S L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (firstMargin m e A B)
      (add (multiply (fraction two one) (gap m e A B S (succ (succ L))))
        (multiply (fraction one (S*num 4)) (meshBudget m e A B))) := by
  let M := S*num 8
  let K := succ (succ L)
  let P := panelPrefix m (e-1) A B M K
  let W := massPrefix e A B M K
  let c : PTm n := fraction two one
  let η := firstMargin m e A B
  let C : PTm n := signedMean (m+1)
  let E := multiply (fraction one (S*num 4)) (meshBudget m e A B)
  let X := multiply c P
  let Y := multiply C (multiply c W)
  have h := uniform_outer_covariance m e he A B S L hA hB hS
  have moved := add_monotone _ _ (negative X) (negative X) h (reflexive _)
  have hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed η := multiply_guard _ _
  have left := (add_congr (add_commutative X η) (.eqRefl _)).eqTrans (add_negative_cancel η X hc)
  have eo := (multiply_associative (Γ := Γ) C c W).eqSymm.eqTrans
    ((multiply_congr (multiply_commutative C c) (.eqRefl _)).eqTrans (multiply_associative c C W))
  have erg : Γ ⊢[PRAAx] add Y (negative X) ≐ multiply c (gap m e A B S K) :=
    (add_congr eo (multiply_negative c P).eqSymm).eqTrans (multiply_add c (multiply C W) (negative P)).eqSymm
  have right := (add_associative Y E (negative X)).eqTrans
    ((add_congr (.eqRefl _) (add_commutative E (negative X))).eqTrans
      ((add_associative _ _ _).eqSymm.eqTrans (add_congr erg (.eqRefl E))))
  exact rationalLE_congr left right moved

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderOuterCovarianceRate
