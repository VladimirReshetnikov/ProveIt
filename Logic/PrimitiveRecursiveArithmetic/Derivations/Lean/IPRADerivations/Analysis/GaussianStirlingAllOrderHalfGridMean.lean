import IPRADerivations.Analysis.GaussianStirlingAllOrderHalfGridMargin

/-!
# A refinement-independent margin between the actual half-grid means

Divide the crossed-product bound by twice the square of the half-grid
length. The separated rectangle therefore retains its original
positive margin divided by 32 at every refinement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderHalfGridMean

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianStirlingAllOrderBoxProductGap (boxMargin box_margin_positive weightDenominator)
open GaussianStirlingAllOrderCrossedRectangles (bernoulliSum reflectedSum pairedSum)
open GaussianStirlingAllOrderHalfGridMargin (leftSide rightSide half_grid_margin)
open RationalAlgebra (add_congr multiply_congr multiply_associative multiply_commutative multiply_add)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add multiply multiply_monotone multiply_guard)
open RationalFiniteSum (canonical_equal)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalNormalForm (normalize_well_formed)
open RationalSumConstants (count_add multiply_one_right)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem same_fraction (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] A*D ≐ C*B) : Γ ⊢[PRAAx] fraction A B ≐ fraction C D := by
  refine canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hB) (normalize_well_formed _ _ hD)
    (fraction_represents _ _ hB) (fraction_represents _ _ hD) hB hD ?_
  apply ZT.derive
  simpa only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] using natEq h

private theorem multiply_four (a b c d : PTm n) : Γ ⊢[PRAAx]
    multiply (multiply a b) (multiply c d) ≐ multiply (multiply a c) (multiply b d) := by
  have mid := (multiply_associative (Γ := Γ) a b c).eqTrans
    ((multiply_congr (.eqRefl _) (multiply_commutative b c)).eqTrans (multiply_associative a c b).eqSymm)
  exact (multiply_associative _ _ _).eqSymm.eqTrans
    ((multiply_congr mid (.eqRefl _)).eqTrans (multiply_associative _ _ _))

noncomputable def margin (m : ℕ) (q A B : PTm n) : PTm n := multiply (fraction one (num 32)) (boxMargin m q A B)

noncomputable def inequality (m : ℕ) (q A B S : PTm n) : Fm PTm n :=
  let N := S*num 4
  let c := fraction one N
  rationalLE (add (multiply c (pairedSum m q A B S zero N)) (margin m q A B))
    (multiply (multiply c (bernoulliSum m q A B S zero N)) (multiply c (reflectedSum q A B S zero N)))

theorem normalized_margin_positive (m : ℕ) (q A B : PTm n)
    (ha : Γ ⊢[PRAAx] le one A) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE
      (fraction one (num 32*GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen m*weightDenominator q A B))
      (margin m q A B) := by
  let D := GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen m*weightDenominator q A B
  let x : PTm n := num 32
  let c := fraction one x
  have hX : Γ ⊢[PRAAx] le one x := by dsimp only [x]; ipra_le 31
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have base : Γ ⊢[PRAAx] le one (num 8*A+B) := le_trans (positive_product _ _ h8 ha) (le_add_right _ _)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _
    (GaussianStirlingAllOrderCenteredBernoulli.denominator_positive _ _ h8)
    (GaussianStirlingAllOrderPairedWeight.gap_denominator_positive _ _ _ _ base)
  have h := multiply_monotone c (fraction one D) (boxMargin m q A B)
    (nonnegative_of_representation c one x hX (fraction_represents _ _ hX)) (box_margin_positive m q A B ha hb)
  have e : Γ ⊢[PRAAx] multiply c (fraction one D) ≐
      fraction one (num 32*GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen m*weightDenominator q A B) :=
    (fraction_multiply one x one D hX hD).eqTrans
    (fraction_congr (one_mul one) (by dsimp only [D,x]; ipra_ring))
  exact rationalLE_congr e (.eqRefl _) h

set_option maxHeartbeats 800000 in
theorem half_grid_mean (m : ℕ) (q A B S : PTm n) (ha : Γ ⊢[PRAAx] le one A)
    (hb : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] inequality m q A B S := by
  let N := S*num 4
  let D := two*N*N
  let scale := fraction one D
  let u := fraction one N
  let H := bernoulliSum m q A B S zero N
  let W := reflectedSum q A B S zero N
  let P := pairedSum m q A B S zero N
  let C := boxMargin m q A B
  let Z := multiply H W
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ hs (by ipra_le 3)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ RationalAlgebra.two_positive hN) hN
  have hp := nonnegative_of_representation scale one D hD (fraction_represents _ _ hD)
  have normal := multiply_monotone scale _ _ hp (half_grid_margin m q A B S ha hb hs)
  have doubleLeft : Γ ⊢[PRAAx] leftSide m q A B S zero zero N N ≐ multiply (fraction (N+N) one) P :=
    (add_congr (multiply_commutative (fraction N one) P) (multiply_commutative (fraction N one) P)).eqTrans
      ((multiply_add P (fraction N one) (fraction N one)).eqSymm.eqTrans
        ((multiply_congr (.eqRefl _) (count_add N N)).eqTrans (multiply_commutative _ _)))
  have doubleRight : Γ ⊢[PRAAx] rightSide m q A B S zero zero N N ≐ multiply (fraction two one) Z := by
    have unit := multiply_one_right (Γ := Γ) Z (multiply_guard _ _)
    have count : Γ ⊢[PRAAx] add (fraction one one) (fraction one one) ≐ fraction two one :=
      (count_add one one).eqTrans (fraction_congr (by ipra_ring) (.eqRefl one))
    exact (add_congr (.eqRefl Z) (multiply_commutative W H)).eqTrans
      ((add_congr unit.eqSymm unit.eqSymm).eqTrans ((multiply_add Z (fraction one one) (fraction one one)).eqSymm.eqTrans
        ((multiply_congr (.eqRefl _) count).eqTrans (multiply_commutative _ _))))
  have lScale : Γ ⊢[PRAAx] multiply scale (fraction (N+N) one) ≐ u :=
    (fraction_multiply one D (N+N) one hD (le_refl one)).eqTrans
      (same_fraction _ _ _ _ (positive_product _ _ hD (le_refl one)) hN (by dsimp only [D]; ipra_ring))
  have dScale : Γ ⊢[PRAAx] multiply scale (fraction (S*S) one) ≐ fraction one (num 32) :=
    (fraction_multiply one D (S*S) one hD (le_refl one)).eqTrans
      (same_fraction _ _ _ _ (positive_product _ _ hD (le_refl one)) (by ipra_le 31) (by dsimp only [D,N]; ipra_ring))
  have rScale : Γ ⊢[PRAAx] multiply scale (fraction two one) ≐ multiply u u :=
    (fraction_multiply one D two one hD (le_refl one)).eqTrans
      ((same_fraction _ _ _ _ (positive_product _ _ hD (le_refl one)) (positive_product _ _ hN hN)
        (by dsimp only [D]; ipra_ring)).eqTrans (fraction_multiply one N one N hN hN).eqSymm)
  have left := (multiply_congr (Γ := Γ) (.eqRefl scale) doubleLeft).eqTrans
    ((multiply_associative _ _ _).eqSymm.eqTrans (multiply_congr lScale (.eqRefl P)))
  have mid : Γ ⊢[PRAAx] multiply scale (multiply (fraction (S*S) one) C) ≐ margin m q A B :=
    (multiply_associative _ _ _).eqSymm.eqTrans (multiply_congr dScale (.eqRefl C))
  have right : Γ ⊢[PRAAx] multiply scale (rightSide m q A B S zero zero N N) ≐ multiply (multiply u H) (multiply u W) :=
    (multiply_congr (.eqRefl scale) doubleRight).eqTrans
      ((multiply_associative _ _ _).eqSymm.eqTrans
        ((multiply_congr rScale (.eqRefl Z)).eqTrans (multiply_four u u H W)))
  exact rationalLE_congr ((multiply_add scale _ _).eqTrans (add_congr left mid)) right normal

theorem actual_reflected_half_grid_mean_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3))) ⟶
        inequality m (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (half_grid_mean m _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderHalfGridMean
