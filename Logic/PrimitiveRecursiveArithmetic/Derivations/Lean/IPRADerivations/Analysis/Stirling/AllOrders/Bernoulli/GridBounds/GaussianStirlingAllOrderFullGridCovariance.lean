import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GridBounds.GaussianStirlingAllOrderHalfGridMean
import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedBernoulliFold
import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedPanel
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalHalfNinthProductLower

/-!
# Strict covariance on the original full left Bernoulli panel

The reflection argument gives a positive margin independent of the
mesh refinement. Doubling the original left panel retains the exact
midpoint row divided by the half-grid length.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFullGridCovariance

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_lower nonnegative_of_representation)
open GaussianStirlingAllOrderBernoulliMeshOrder (sample_nonnegative_first_half)
open GaussianStirlingAllOrderCrossedCells (bernoulliBody bernoulli_at segmentData)
open GaussianStirlingAllOrderCrossedRectangles (bernoulliSum pairedSum reflectedSum)
open GaussianStirlingAllOrderHalfGridMean (margin half_grid_mean)
open GaussianStirlingAllOrderKernel (row multiply_zero_right)
open GaussianStirlingAllOrderPairedRefinement (mesh start)
open GaussianStirlingAllOrderPairedWeight (weight)
open GaussianStirlingAllOrderPairedWeightFold (singleWeight weightBody weightData weight_row_at weightAverage double_scale)
open GaussianStirlingAllOrderPanelTail (panel)
open RationalAlgebra (add_associative add_commutative add_congr multiply_add multiply_commutative multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add multiply negative add_guard multiply_guard multiply_monotone)
open RationalFiniteSum (sum sum_monotone term termwiseLE)
open RationalGaussianEmbedding (scalarZero)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalNormalForm (normalize_well_formed wellFormed)
open RationalReciprocalPowerTail (add_zero_right)
open RationalSumConstants (constantBody term_constant sum_constant)
open GaussianRationalSyntheticBounds (add_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "z" => fraction zero one

noncomputable def fullMean (m : ℕ) (q U B S : PTm n) : PTm n :=
  multiply (fraction one (S*num 8)) (bernoulliSum m q U B S zero (S*num 8))

def doubledWeight (q U B S : PTm n) : PTm n :=
  multiply (fraction two one) (weightAverage q U B S)

noncomputable def midpointCorrection (m : ℕ) (q A B S k : PTm n) : PTm n :=
  multiply (fraction one (S*num 4)) (row m q A B (S*num 8) k (S*num 4))

noncomputable def comparison (m : ℕ) (q A B S k : PTm n) : Fm PTm n :=
  let U := A+B*k
  rationalLE (add (multiply (fraction two one) (panel m q A B (S*num 8) k)) (margin m q U B))
    (add (multiply (fullMean m q U B S) (doubledWeight q U B S)) (midpointCorrection m q A B S k))

private theorem scalar_fraction_nonnegative (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] rationalLE z (fraction a b) :=
  fraction_order _ _ _ _ (le_refl one) hb
    (le_congr (by ipra_ring) (by ipra_ring) (zero_le a))

private theorem zero_sign : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign (z : PTm n) :=
  nonnegative_of_representation _ _ _ (le_refl one) (fraction_represents zero one (le_refl one))

private theorem scaled_nonnegative (c t : PTm n) (hc : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign c)
    (ht : Γ ⊢[PRAAx] rationalLE z t) : Γ ⊢[PRAAx] rationalLE z (multiply c t) :=
  rationalLE_congr (multiply_zero_right c) (.eqRefl _) (multiply_monotone c _ _ hc ht)

private theorem sum_nonnegative (f : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] termwiseLE constantBody f N z x) : Γ ⊢[PRAAx] rationalLE z (sum f N x) := by
  have e := sum_constant (Γ := Γ) N (z : PTm n) (normalize_well_formed _ _ (le_refl one))
  have e' := (multiply_commutative (Γ := Γ) (z : PTm n) (fraction N one)).eqTrans (multiply_zero_right _)
  exact rationalLE_congr (e.eqTrans e') (.eqRefl _) (sum_monotone constantBody f N z x h)

private theorem half_bernoulli_nonnegative (m : ℕ) (q U B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE z (bernoulliSum m q U B S zero (S*num 4)) := by
  refine sum_nonnegative _ _ _ (.allI (.impI ?_))
  let T := Syn.shift S
  let i : PTm (n+1) := var 0
  let Δ := lt i (T*num 4) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (T*num 4) := Prf.hyp0
  have hs : Δ ⊢[PRAAx] le one T := (by simpa [Fm.shift,Syn.shift,T] using hS.shift : Γ.map Fm.shift ⊢[PRAAx] le one T).wk
  have hM : Δ ⊢[PRAAx] le one (T*num 8) := positive_product _ _ hs (by ipra_le 7)
  have pos : Δ ⊢[PRAAx] le (two*(zero+i)) (T*num 8) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl two) (le_of_lt hi))
  have r := sample_nonnegative_first_half m (zero+i) (T*num 8) hM pos
  have e := bernoulli_at (Γ := Δ) m i (Syn.shift q) (Syn.shift U) (Syn.shift B) T zero
  simpa [termwiseLE,term_constant,Syn.shift,T,i,Δ] using rationalLE_congr (.eqRefl _) e.eqSymm r

private theorem weight_den_positive (U S : PTm n) (hU : Γ ⊢[PRAAx] le one U) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] le one (start U S) :=
  positive_product _ _ hS (positive_product _ _ (by ipra_le 7) hU)

private theorem single_weight_nonnegative (q U B S i : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx] rationalLE z (singleWeight q U B S i) :=
  scalar_fraction_nonnegative _ _ (GaussianFactorBudget.power_positive _ _
    (le_trans (weight_den_positive U S hU hS) (le_add_right _ _)))

theorem doubled_weight_nonnegative (q U B S : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign (doubledWeight q U B S) := by
  have hSum : Γ ⊢[PRAAx] rationalLE z (sum weightBody (S*num 8) (weightData q U B S)) := by
    refine sum_nonnegative _ _ _ (.allI (.impI ?_))
    let T := Syn.shift S
    let V := Syn.shift U
    let i : PTm (n+1) := var 0
    let Δ := lt i (T*num 8) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] le one T := (by simpa [Fm.shift,Syn.shift,T] using hS.shift : Γ.map Fm.shift ⊢[PRAAx] le one T).wk
    have hu : Δ ⊢[PRAAx] le one V := (by simpa [Fm.shift,Syn.shift,V] using hU.shift : Γ.map Fm.shift ⊢[PRAAx] le one V).wk
    have e := weight_row_at (Γ := Δ) i (Syn.shift q) V (Syn.shift B) T
    have r := single_weight_nonnegative (Syn.shift q) V (Syn.shift B) T i hu hs
    simpa [termwiseLE,term_constant,Syn.shift,T,V,i,Δ] using rationalLE_congr (.eqRefl _) e.eqSymm r
  have hM : Γ ⊢[PRAAx] le one (S*num 8) := positive_product _ _ hS (by ipra_le 7)
  have hScale := nonnegative_of_representation _ _ _ hM (fraction_represents one (S*num 8) hM)
  have twoSign := nonnegative_of_representation (Γ := Γ) (fraction two one) two one (le_refl one)
    (fraction_represents _ _ (le_refl one))
  exact nonnegative_of_lower _ _ zero_sign (scaled_nonnegative _ _ twoSign (scaled_nonnegative _ _ hScale hSum))

private theorem single_weight_decreasing (q U B S i j : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] le one S) (hij : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] rationalLE (singleWeight q U B S j) (singleWeight q U B S i) := by
  let G := mesh B S
  let x := start U S+B*i
  let y := start U S+B*j
  let e := succ q
  have hx : Γ ⊢[PRAAx] le one x := le_trans (weight_den_positive U S hU hS) (le_add_right _ _)
  have hxy : Γ ⊢[PRAAx] le x y := by unfold x y; ipra_le Groth.ι (IPRA.Q.mk Γ B)*sl hij
  have hy := le_trans hx hxy
  exact fraction_order (pw G e) (pw y e) (pw G e) (pw x e)
    (GaussianFactorBudget.power_positive _ _ hy) (GaussianFactorBudget.power_positive _ _ hx)
    (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (pw_le_pw e hxy) (le_refl (pw G e))))

theorem half_weight_le (q U B S : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (multiply (fraction one (S*num 4)) (reflectedSum q U B S zero (S*num 4)))
      (doubledWeight q U B S) := by
  let N := S*num 4
  let M := S*num 8
  let c := fraction one N
  let W := multiply c (reflectedSum q U B S zero N)
  let R := multiply c (singleWeight q U B S M)
  let T := multiply c (singleWeight q U B S N)
  let D := doubledWeight q U B S
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ hS (by ipra_le 3)
  have hNM : Γ ⊢[PRAAx] le N M := by unfold N M; ipra_le 4*Groth.ι (IPRA.Q.mk Γ S)
  have hc := nonnegative_of_representation c one N hN (fraction_represents _ _ hN)
  have edge := multiply_monotone c _ _ hc (single_weight_decreasing q U B S N M hU hS hNM)
  have both := add_monotone W W R T (reflexive _) edge
  have translated := rationalLE_congr (.eqRefl _) (GaussianStirlingAllOrderPairedWeightFold.weight_average q U B S hS).eqSymm both
  have cancel := add_monotone _ _ (negative R) (negative R) translated (reflexive _)
  exact rationalLE_congr (add_negative_cancel W R (multiply_guard _ _))
    (add_negative_cancel D R (multiply_guard _ _)) cancel

theorem half_bernoulli_le (m : ℕ) (q U B S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (multiply (fraction one (S*num 4)) (bernoulliSum m q U B S zero (S*num 4)))
      (fullMean m q U B S) := by
  let N := S*num 4
  let M := S*num 8
  let c := fraction one M
  let H := multiply (fraction one N) (bernoulliSum m q U B S zero N)
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have h := sample_nonnegative_first_half m N M hM (le_of_eq_add (d := zero) (by unfold N M; ipra_ring))
  have step := scaled_nonnegative c _ (nonnegative_of_representation c one M hM (fraction_represents _ _ hM)) h
  have right := GaussianStirlingAllOrderPairedBernoulliFold.bernoulli_average m q U B S hS
  exact rationalLE_congr (add_zero_right H (multiply_guard _ _)) right.eqSymm
    (add_monotone H H _ _ (reflexive _) step)

theorem full_panel_identity (m : ℕ) (q A B S k : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] multiply (fraction two one) (panel m q A B (S*num 8) k) ≐
      add (multiply (fraction one (S*num 4)) (pairedSum m q (A+B*k) B S zero (S*num 4)))
        (midpointCorrection m q A B S k) := by
  let N := S*num 4
  let U := A+B*k
  let P := pairedSum m q U B S zero N
  let R := row m q A B (S*num 8) k N
  have e := GaussianStirlingAllOrderPairedPanel.original_panel m q A B S k hS
  exact (multiply_congr (.eqRefl _) e).eqTrans
    ((double_scale S (add P R) hS).eqTrans (multiply_add _ _ _))

theorem full_grid_covariance (m : ℕ) (q A B S k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] comparison m q A B S k := by
  let U := A+B*k
  let N := S*num 4
  let P := multiply (fraction one N) (pairedSum m q U B S zero N)
  let H := multiply (fraction one N) (bernoulliSum m q U B S zero N)
  let W := multiply (fraction one N) (reflectedSum q U B S zero N)
  let G := fullMean m q U B S
  let V := doubledWeight q U B S
  let T := midpointCorrection m q A B S k
  let E := margin m q U B
  have hU : Γ ⊢[PRAAx] le one U := le_trans hA (le_add_right _ _)
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ hS (by ipra_le 3)
  have hH := nonnegative_of_lower z H zero_sign
    (scaled_nonnegative _ _ (nonnegative_of_representation _ _ _ hN (fraction_represents one N hN))
      (half_bernoulli_nonnegative m q U B S hS))
  have hV := doubled_weight_nonnegative q U B S hU hS
  have w := multiply_monotone H W V hH (half_weight_le q U B S hU hS)
  have b := rationalLE_congr (multiply_commutative V H) (multiply_commutative V G)
    (multiply_monotone V H G hV (half_bernoulli_le m q U B S hS))
  have start : Γ ⊢[PRAAx] rationalLE (add P E) (multiply H W) := half_grid_mean m q U B S hU hB hS
  have joined := add_monotone _ _ T T (transitive (transitive start w) b) (reflexive _)
  have sort := (add_associative (Γ := Γ) P E T).eqTrans
    ((add_congr (.eqRefl _) (add_commutative E T)).eqTrans (add_associative P T E).eqSymm)
  have rebalance := sort.eqTrans (add_congr (full_panel_identity m q A B S k hS).eqSymm (.eqRefl _))
  exact rationalLE_congr rebalance (.eqRefl _) joined

theorem actual_original_full_left_panel_covariance_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
        comparison m (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (full_grid_covariance m _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFullGridCovariance
